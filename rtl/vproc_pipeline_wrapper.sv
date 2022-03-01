// Copyright TU Wien
// Licensed under the Solderpad Hardware License v2.1, see LICENSE.txt for details
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1


module vproc_pipeline_wrapper #(
        parameter int unsigned          VREG_W              = 128,  // width in bits of vector registers
        parameter int unsigned          CFG_VL_W            = 7,    // width of VL reg in bits (= log2(VREG_W))
        parameter int unsigned          XIF_ID_W            = 3,    // width in bits of instruction IDs
        parameter int unsigned          XIF_ID_CNT          = 8,    // total count of instruction IDs
        parameter vproc_pkg::op_unit    UNIT                = vproc_pkg::UNIT_ALU,
        parameter int unsigned          MAX_VPORT_W         = 128,  // max port width
        parameter int unsigned          MAX_VADDR_W         = 5,    // max addr width
        parameter int unsigned          VPORT_CNT           = 1,
        parameter int unsigned          VPORT_W [VPORT_CNT] = '{0},
        parameter int unsigned          VADDR_W [VPORT_CNT] = '{0},
        parameter bit [VPORT_CNT-1:0]   VPORT_ADDR_ZERO     = '0,   // set addr to 0
        parameter bit [VPORT_CNT-1:0]   VPORT_BUFFER        = '0,   // buffer port
        parameter int unsigned          MAX_OP_W            = 64,   // operand width in bits
        parameter vproc_pkg::mul_type   MUL_TYPE            = vproc_pkg::MUL_GENERIC,
        parameter bit                   ADDR_ALIGNED        = 1'b1, // base address is aligned to VMEM_W
        parameter int unsigned          MAX_WR_ATTEMPTS     = 1,    // max required vregfile write attempts
        parameter type                  DECODER_DATA_T      = logic,
        parameter bit                   DONT_CARE_ZERO      = 1'b0  // initialize don't care values to zero
    )(
        input  logic                    clk_i,
        input  logic                    async_rst_ni,
        input  logic                    sync_rst_ni,

        input  logic                    pipe_in_valid_i,
        output logic                    pipe_in_ready_o,
        input  DECODER_DATA_T           pipe_in_data_i,

        input  logic [31:0]             vreg_pend_wr_i,
        output logic [31:0]             vreg_pend_rd_o,
        input  logic [31:0]             vreg_pend_rd_i,

        output logic [31:0]             clear_wr_hazards_o,

        input  logic [XIF_ID_CNT-1:0]   instr_spec_i,
        input  logic [XIF_ID_CNT-1:0]   instr_killed_i,
        output logic                    instr_done_valid_o,
        output logic [XIF_ID_W-1:0]     instr_done_id_o,

        output logic [VPORT_CNT-1:0][MAX_VADDR_W-1:0] vreg_rd_addr_o,       // vreg read address
        input  logic [VPORT_CNT-1:0][MAX_VPORT_W-1:0] vreg_rd_data_i,       // vreg read data

        output logic [VREG_W-1:0]       vreg_wr_o,
        output logic [4:0]              vreg_wr_addr_o,
        output logic [VREG_W/8-1:0]     vreg_wr_mask_o,
        output logic                    vreg_wr_en_o,

        output logic                    pending_load_o,
        output logic                    pending_store_o,

        vproc_xif.coproc_mem            xif_mem_if,
        vproc_xif.coproc_mem_result     xif_memres_if,

        output logic                    trans_complete_valid_o,
        output logic [XIF_ID_W-1:0]     trans_complete_id_o,
        output logic                    trans_complete_exc_o,
        output logic [5:0]              trans_complete_exccode_o,

        output logic                    xreg_valid_o,
        output logic [XIF_ID_W-1:0]     xreg_id_o,
        output logic [4:0]              xreg_addr_o,
        output logic [31:0]             xreg_data_o
    );

    import vproc_pkg::*;

    localparam int unsigned OP_CNT     = ((UNIT == UNIT_MUL) | (UNIT == UNIT_ELEM)) ? 4 : (
                                          (UNIT == UNIT_SLD)                        ? 2 : 3);

    // operand widths
    localparam int unsigned DFLT_OP_W  = (UNIT == UNIT_ELEM) ? 32 : MAX_OP_W;    // default width
    localparam int unsigned FIRST_OP_W = (UNIT == UNIT_LSU ) ? 32 : DFLT_OP_W;   // first operand
    localparam int unsigned EXTRA_OP_W = MAX_OP_W;                               // extra operand
    localparam int unsigned MASK_OP_W  = (UNIT == UNIT_ELEM) ? 1  : DFLT_OP_W/8; // v0 mask width

    // operand flags
    localparam bit EXTRA_OP_ADDR_OFFSET  = UNIT == UNIT_ELEM;
    localparam bit SECOND_OP_MASK        = UNIT == UNIT_ELEM;
    localparam bit FIRST_OP_XREG         = (UNIT == UNIT_MUL) | (UNIT == UNIT_ALU);
    localparam bit FIRST_OP_NARROW       = (UNIT == UNIT_MUL) | (UNIT == UNIT_ALU) | (UNIT == UNIT_ELEM);
    localparam bit SECOND_OP_NARROW      = (UNIT == UNIT_MUL) | (UNIT == UNIT_ALU);
    localparam bit ALL_OP_ELEMWISE       = UNIT == UNIT_ELEM;
    localparam bit FIRST_OP_ELEMWISE     = UNIT == UNIT_LSU;
    localparam bit FIRST_OP_HOLD_FLAG    = UNIT == UNIT_ELEM;
    localparam bit FIRST_OP_ALT_COUNTER  = UNIT == UNIT_SLD;
    localparam bit FIRST_OP_ALWAYS_VREG  = UNIT == UNIT_SLD;
    localparam bit SECOND_OP_ALWAYS_VREG = 1'b0; // UNIT == UNIT_SLD;
    localparam bit EXTRA_OP_ALWAYS_VREG  = 1'b0; // UNIT == UNIT_SLD;

    // number of stages for operand unpacking
    localparam int unsigned UNPACK_STAGES = (UNIT == UNIT_SLD) ? 2 : ((UNIT == UNIT_ELEM) ? 4 : 3);

    // result count and default width
    localparam int unsigned RES_CNT   = (UNIT == UNIT_ALU ) ? 2  : 1;
    localparam int unsigned MAX_RES_W = (UNIT == UNIT_ELEM) ? 32 : MAX_OP_W;

    // result flags
    localparam bit FIRST_RES_ALWAYS_VREG     = (UNIT != UNIT_LSU) & (UNIT != UNIT_ELEM);
    localparam bit FIRST_RES_NARROW          = UNIT == UNIT_ALU;
    localparam bit FIRST_RES_ALLOW_ELEMWISE  = UNIT == UNIT_LSU;
    localparam bit FIRST_RES_ALWAYS_ELEMWISE = UNIT == UNIT_ELEM;

    // other pipeline flags
    localparam bit MAY_FLUSH = UNIT == UNIT_ELEM;   // the pipeline may require flushing


    ///////////////////////////////////////////////////////////////////////////
    // CONVERT DECODER DATA TO INITIAL PIPELINE STATE

    localparam int unsigned ALT_COUNT_W = $clog2(VREG_W/MAX_OP_W) + 4;

    typedef struct packed {
        logic                            count_extra_phase; // start by counting an extra phase
        logic        [ALT_COUNT_W  -1:0] alt_count_init;    // alternative counter init value
        count_inc_e                      count_inc;         // counter increment policy
        logic                            requires_flush;    // whether the instr requires flushing
        logic        [XIF_ID_W     -1:0] id;
        op_mode                          mode;
        cfg_vsew                         eew;               // effective element width
        cfg_emul                         emul;              // effective MUL factor
        cfg_vxrm                         vxrm;
        logic        [CFG_VL_W     -1:0] vl;
        logic                            vl_0;
        logic                     [31:0] xval;
        unpack_flags [OP_CNT -1:0]       op_flags;
        logic        [OP_CNT -1:0][4 :0] op_vaddr;
        logic        [OP_CNT -1:0][31:0] op_xval;
        logic        [RES_CNT-1:0]       res_vreg;
        logic        [RES_CNT-1:0]       res_narrow;
        logic                     [4 :0] res_vaddr;
    } state_t;

    logic op_reduction;
    always_comb begin
        op_reduction = DONT_CARE_ZERO ? 1'b0 : 1'bx;
        unique case (pipe_in_data_i.mode.elem.op)
            ELEM_XMV:       op_reduction = 1'b0;
            ELEM_VPOPC:     op_reduction = 1'b0;
            ELEM_VFIRST:    op_reduction = 1'b0;
            ELEM_VID:       op_reduction = 1'b0;
            ELEM_VIOTA:     op_reduction = 1'b0;
            ELEM_VRGATHER:  op_reduction = 1'b0;
            ELEM_VCOMPRESS: op_reduction = 1'b0;
            ELEM_FLUSH:     op_reduction = 1'b0;
            ELEM_VREDSUM:   op_reduction = 1'b1;
            ELEM_VREDAND:   op_reduction = 1'b1;
            ELEM_VREDOR:    op_reduction = 1'b1;
            ELEM_VREDXOR:   op_reduction = 1'b1;
            ELEM_VREDMINU:  op_reduction = 1'b1;
            ELEM_VREDMIN:   op_reduction = 1'b1;
            ELEM_VREDMAXU:  op_reduction = 1'b1;
            ELEM_VREDMAX:   op_reduction = 1'b1;
            default: ;
        endcase
    end

    state_t state_init;
    always_comb begin
        state_init = state_t'('0);

        state_init.count_extra_phase = (UNIT == UNIT_SLD) & (pipe_in_data_i.mode.sld.dir == SLD_DOWN);
        state_init.alt_count_init    = '0;
        if (UNIT == UNIT_SLD) begin
            state_init.alt_count_init = DONT_CARE_ZERO ? '0 : 'x;
            if (pipe_in_data_i.mode.sld.slide1) begin
                if (pipe_in_data_i.mode.sld.dir == SLD_UP) begin
                    // slide counter is all zeroes for up slide, except for a byte slide of 4
                    // when the operand width is 32 bits, then it is 1, since the counter then
                    // captures all but the 2 lowest bits of the byte slide value
                    unique case (pipe_in_data_i.vsew)
                        VSEW_8,
                        VSEW_16: state_init.alt_count_init = '0;
                        VSEW_32: state_init.alt_count_init = {{ALT_COUNT_W-1{1'b0}}, MAX_OP_W == 32};
                        default: ;
                    endcase
                end else begin
                    // slide counter is all ones for down slide, even with a byte slide value of
                    // -4 since this has no effect on any but the 2 lowest bits of the byte
                    // slide value
                    state_init.alt_count_init = {4'b1111, {(ALT_COUNT_W-5){1'b0}}, 1'b1};
                end
            end
            else if (pipe_in_data_i.mode.sld.dir == SLD_UP) begin
                unique case (pipe_in_data_i.vsew)
                    VSEW_8:  state_init.alt_count_init = -{1'b0, pipe_in_data_i.rs1.r.xval[$clog2(MAX_OP_W/8)   +: ALT_COUNT_W-1]};
                    VSEW_16: state_init.alt_count_init = -{1'b0, pipe_in_data_i.rs1.r.xval[$clog2(MAX_OP_W/8)-1 +: ALT_COUNT_W-1]};
                    VSEW_32: state_init.alt_count_init = -{1'b0, pipe_in_data_i.rs1.r.xval[$clog2(MAX_OP_W/8)-2 +: ALT_COUNT_W-1]};
                    default: ;
                endcase
            end else begin
                unique case (pipe_in_data_i.vsew)
                    VSEW_8:  state_init.alt_count_init = ALT_COUNT_W'((
                        {4'b1111, {(ALT_COUNT_W-4){1'b0}}, {$clog2(MAX_OP_W/8){1'b1}}} +
                        {1'b0, pipe_in_data_i.rs1.r.xval[$clog2(VREG_W/8)+2:0]      }
                    ) >> $clog2(MAX_OP_W/8));
                    VSEW_16: state_init.alt_count_init = ALT_COUNT_W'((
                        {4'b1111, {(ALT_COUNT_W-4){1'b0}}, {$clog2(MAX_OP_W/8){1'b1}}} +
                        {1'b0, pipe_in_data_i.rs1.r.xval[$clog2(VREG_W/8)+1:0], 1'b0}
                    ) >> $clog2(MAX_OP_W/8));
                    VSEW_32: state_init.alt_count_init = ALT_COUNT_W'((
                        {4'b1111, {(ALT_COUNT_W-4){1'b0}}, {$clog2(MAX_OP_W/8){1'b1}}} +
                        {1'b0, pipe_in_data_i.rs1.r.xval[$clog2(VREG_W/8)+0:0], 2'b0}
                    ) >> $clog2(MAX_OP_W/8));
                    default: ;
                endcase
            end
        end

        state_init.count_inc = COUNT_INC_1;
        //if ((OP_ALLOW_ELEMWISE != '0) | (OP_ALWAYS_ELEMWISE != '0)) begin
        if ((UNIT == UNIT_LSU) | (UNIT == UNIT_ELEM)) begin
            state_init.count_inc = DONT_CARE_ZERO ? count_inc_e'('0) : count_inc_e'('x);
            unique case ((UNIT == UNIT_LSU) ? pipe_in_data_i.mode.lsu.eew : pipe_in_data_i.vsew)
                VSEW_8:  state_init.count_inc = COUNT_INC_1;
                VSEW_16: state_init.count_inc = COUNT_INC_2;
                VSEW_32: state_init.count_inc = COUNT_INC_4;
                default: ;
            endcase
        end
        if ((UNIT == UNIT_LSU) & (pipe_in_data_i.mode.lsu.stride == LSU_UNITSTRIDE)) begin
            state_init.count_inc = COUNT_INC_MAX;
        end

        state_init.requires_flush = (UNIT == UNIT_ELEM) & ((pipe_in_data_i.mode.elem.op == ELEM_VCOMPRESS) | op_reduction);
        state_init.id             = pipe_in_data_i.id;
        state_init.mode           = pipe_in_data_i.mode;
        state_init.emul           = pipe_in_data_i.emul;
        state_init.eew            = (UNIT == UNIT_LSU) ? pipe_in_data_i.mode.lsu.eew : pipe_in_data_i.vsew;
        state_init.vxrm           = pipe_in_data_i.vxrm;
        state_init.vl             = pipe_in_data_i.vl;
        state_init.vl_0           = pipe_in_data_i.vl_0;
        state_init.xval           = pipe_in_data_i.rs1.r.xval;
        if ((UNIT == UNIT_SLD) & ~pipe_in_data_i.mode.sld.slide1) begin
            // convert element offset to byte offset for the relevant section of rs1 and negate
            // for down slides
            if (pipe_in_data_i.mode.sld.dir == SLD_UP) begin
                unique case (pipe_in_data_i.vsew)
                    VSEW_8:  state_init.xval[$clog2(VREG_W/8)+3:0] =  {1'b0, pipe_in_data_i.rs1.r.xval[$clog2(VREG_W/8)+2:0]      };
                    VSEW_16: state_init.xval[$clog2(VREG_W/8)+3:0] =  {1'b0, pipe_in_data_i.rs1.r.xval[$clog2(VREG_W/8)+1:0], 1'b0};
                    VSEW_32: state_init.xval[$clog2(VREG_W/8)+3:0] =  {1'b0, pipe_in_data_i.rs1.r.xval[$clog2(VREG_W/8)+0:0], 2'b0};
                    default: ;
                endcase
            end else begin
                unique case (pipe_in_data_i.vsew)
                    VSEW_8:  state_init.xval[$clog2(VREG_W/8)+3:0] = -{1'b0, pipe_in_data_i.rs1.r.xval[$clog2(VREG_W/8)+2:0]      };
                    VSEW_16: state_init.xval[$clog2(VREG_W/8)+3:0] = -{1'b0, pipe_in_data_i.rs1.r.xval[$clog2(VREG_W/8)+1:0], 1'b0};
                    VSEW_32: state_init.xval[$clog2(VREG_W/8)+3:0] = -{1'b0, pipe_in_data_i.rs1.r.xval[$clog2(VREG_W/8)+0:0], 2'b0};
                    default: ;
                endcase
            end
        end

        state_init.op_flags[0]        = unpack_flags'('0);
        state_init.op_flags[1]        = unpack_flags'('0);
        state_init.op_flags[OP_CNT-2] = unpack_flags'('0);
        state_init.op_flags[OP_CNT-1] = unpack_flags'('0);
        if ((UNIT == UNIT_LSU) | (UNIT == UNIT_SLD)) begin
            state_init.op_flags[0].vreg   = pipe_in_data_i.rs2.vreg;
            state_init.op_vaddr[0]        = pipe_in_data_i.rs2.r.vaddr;
            state_init.op_xval [0]        = pipe_in_data_i.rs2.r.xval;
            state_init.op_flags[1].vreg   = pipe_in_data_i.mode.lsu.store;
            state_init.op_vaddr[1]        = pipe_in_data_i.rd.addr;
        end else begin
            state_init.op_flags[0].vreg   = ((UNIT == UNIT_ELEM) & ((pipe_in_data_i.mode.elem.op == ELEM_XMV) | op_reduction)) | pipe_in_data_i.rs1.vreg;
            state_init.op_flags[0].narrow = pipe_in_data_i.widenarrow != OP_SINGLEWIDTH;
            state_init.op_flags[0].sigext = ((UNIT == UNIT_ALU ) & pipe_in_data_i.mode.alu.sigext) |
                                            ((UNIT == UNIT_MUL ) & pipe_in_data_i.mode.mul.op1_signed) |
                                            ((UNIT == UNIT_ELEM) & pipe_in_data_i.mode.elem.sigext);
            //state_init.op_vaddr[0]        = pipe_in_data_i.rs1.r.vaddr;
            state_init.op_vaddr[0]        = ((UNIT == UNIT_ELEM) &
                                            ((pipe_in_data_i.mode.elem.op == ELEM_XMV) | op_reduction)) ? pipe_in_data_i.rs2.r.vaddr : pipe_in_data_i.rs1.r.vaddr;
            state_init.op_xval [0]        = pipe_in_data_i.rs1.r.xval;
            state_init.op_flags[1].vreg   = pipe_in_data_i.rs2.vreg;
            state_init.op_flags[1].narrow = pipe_in_data_i.widenarrow == OP_WIDENING;
            state_init.op_flags[1].sigext = ((UNIT == UNIT_ALU) & pipe_in_data_i.mode.alu.sigext) | ((UNIT == UNIT_MUL) & pipe_in_data_i.mode.mul.op2_signed);
            //state_init.op_vaddr[1]        = pipe_in_data_i.rs2.r.vaddr;
            state_init.op_vaddr[1]        = ((UNIT == UNIT_ELEM) & op_reduction) ? pipe_in_data_i.rs1.r.vaddr : pipe_in_data_i.rs2.r.vaddr;
            if (UNIT == UNIT_MUL) begin
                state_init.op_vaddr[1]             = pipe_in_data_i.mode.mul.op2_is_vd ? pipe_in_data_i.rd.addr : pipe_in_data_i.rs2.r.vaddr;
                state_init.op_flags[OP_CNT-2].vreg = pipe_in_data_i.mode.mul.op == MUL_VMACC;
                state_init.op_vaddr[OP_CNT-2]      = pipe_in_data_i.mode.mul.op2_is_vd ? pipe_in_data_i.rs2.r.vaddr : pipe_in_data_i.rd.addr;
            end
            if (UNIT == UNIT_ELEM) begin
                state_init.op_flags[1].vreg        = (((UNIT == UNIT_ELEM) & op_reduction) | pipe_in_data_i.rs2.vreg) & (pipe_in_data_i.mode.elem.op != ELEM_VRGATHER);
                state_init.op_flags[OP_CNT-2].vreg = pipe_in_data_i.mode.elem.op == ELEM_VRGATHER;
                state_init.op_vaddr[OP_CNT-2]      = pipe_in_data_i.rs2.r.vaddr;
            end
        end
        unique case (UNIT)
            UNIT_LSU:  state_init.op_flags[OP_CNT-1].vreg = pipe_in_data_i.mode.lsu.masked;
            UNIT_ALU:  state_init.op_flags[OP_CNT-1].vreg = pipe_in_data_i.mode.alu.op_mask != ALU_MASK_NONE;
            UNIT_MUL:  state_init.op_flags[OP_CNT-1].vreg = pipe_in_data_i.mode.mul.masked;
            UNIT_SLD:  state_init.op_flags[OP_CNT-1].vreg = pipe_in_data_i.mode.sld.masked;
            UNIT_ELEM: state_init.op_flags[OP_CNT-1].vreg = pipe_in_data_i.mode.elem.masked;
            default: ;
        endcase
        state_init.op_flags[OP_CNT-1].elemwise = (UNIT == UNIT_LSU) & (pipe_in_data_i.mode.lsu.stride != LSU_UNITSTRIDE);

        state_init.res_vreg  [0] = (UNIT != UNIT_LSU) | ~pipe_in_data_i.mode.lsu.store;
        state_init.res_narrow[0] = (UNIT == UNIT_ALU) ? (pipe_in_data_i.widenarrow == OP_NARROWING) : '0;
        state_init.res_vaddr     = pipe_in_data_i.rd.addr;
        if (UNIT == UNIT_ALU) begin
            state_init.res_vreg [0        ] = ~pipe_in_data_i.mode.alu.cmp;
            state_init.res_vreg [RES_CNT-1] =  pipe_in_data_i.mode.alu.cmp;
        end
    end


    ///////////////////////////////////////////////////////////////////////////
    // PIPELINE INSTANTIATION

    generate
        if (OP_CNT == 2 && RES_CNT == 1) begin
            localparam int unsigned OP_W           [2] = '{FIRST_OP_W, MASK_OP_W};
            localparam int unsigned OP_STAGE       [2] = '{1, UNPACK_STAGES-1};
            localparam int unsigned OP_SRC         [2] = '{0, VPORT_CNT-1};
            localparam bit [1:0]    OP_ADDR_OFFSET_OP0 = '0;
            localparam bit [1:0]    OP_MASK            = 2'b10;
            localparam bit [1:0]    OP_XREG            = FIRST_OP_XREG   ? 2'b01 : '0;
            localparam bit [1:0]    OP_NARROW          = FIRST_OP_NARROW ? 2'b01 : '0;
            // if the first operand is always element-wise, then all other operands are optionally
            localparam bit [1:0]    OP_ALLOW_ELEMWISE  = FIRST_OP_ELEMWISE ? 2'b10 : '0;
            localparam bit [1:0]    OP_ALWAYS_ELEMWISE = ~ALL_OP_ELEMWISE  ? {1'b0, FIRST_OP_ELEMWISE} : '1;
            localparam bit [1:0]    OP_HOLD_FLAG       = FIRST_OP_HOLD_FLAG   ? 2'b01 : '0;
            localparam bit [1:0]    OP_ALT_COUNTER     = FIRST_OP_ALT_COUNTER ? 2'b01 : '0;
            localparam bit [1:0]    OP_ALWAYS_VREG     = FIRST_OP_ALWAYS_VREG ? 2'b01 : '0;

            localparam int unsigned RES_W           [1] = '{MAX_RES_W};
            localparam bit [0:0]    RES_MASK            = '0;
            localparam bit [0:0]    RES_XREG            = '0;
            localparam bit [0:0]    RES_NARROW          = FIRST_RES_NARROW;
            localparam bit [0:0]    RES_ALLOW_ELEMWISE  = FIRST_RES_ALLOW_ELEMWISE;
            localparam bit [0:0]    RES_ALWAYS_ELEMWISE = FIRST_RES_ALWAYS_ELEMWISE;
            localparam bit [0:0]    RES_ALWAYS_VREG     = '0;

            vproc_pipeline #(
                .VREG_W              ( VREG_W              ),
                .CFG_VL_W            ( CFG_VL_W            ),
                .XIF_ID_W            ( XIF_ID_W            ),
                .XIF_ID_CNT          ( XIF_ID_CNT          ),
                .UNIT                ( UNIT                ),
                .MAX_VPORT_W         ( MAX_VPORT_W         ),
                .MAX_VADDR_W         ( MAX_VADDR_W         ),
                .VPORT_CNT           ( VPORT_CNT           ),
                .VPORT_W             ( VPORT_W             ),
                .VADDR_W             ( VADDR_W             ),
                .VPORT_ADDR_ZERO     ( VPORT_ADDR_ZERO     ),
                .VPORT_BUFFER        ( VPORT_BUFFER        ),
                .MAX_OP_W            ( MAX_OP_W            ),
                .OP_CNT              ( OP_CNT              ),
                .OP_W                ( OP_W                ),
                .OP_STAGE            ( OP_STAGE            ),
                .OP_SRC              ( OP_SRC              ),
                .OP_ADDR_OFFSET_OP0  ( OP_ADDR_OFFSET_OP0  ),
                .OP_MASK             ( OP_MASK             ),
                .OP_XREG             ( OP_XREG             ),
                .OP_NARROW           ( OP_NARROW           ),
                .OP_ALLOW_ELEMWISE   ( OP_ALLOW_ELEMWISE   ),
                .OP_ALWAYS_ELEMWISE  ( OP_ALWAYS_ELEMWISE  ),
                .OP_HOLD_FLAG        ( OP_HOLD_FLAG        ),
                .OP_ALT_COUNTER      ( OP_ALT_COUNTER      ),
                .OP_ALWAYS_VREG      ( OP_ALWAYS_VREG      ),
                .UNPACK_STAGES       ( UNPACK_STAGES       ),
                .MAX_RES_W           ( MAX_RES_W           ),
                .RES_CNT             ( RES_CNT             ),
                .RES_W               ( RES_W               ),
                .RES_MASK            ( RES_MASK            ),
                .RES_XREG            ( RES_XREG            ),
                .RES_NARROW          ( RES_NARROW          ),
                .RES_ALLOW_ELEMWISE  ( RES_ALLOW_ELEMWISE  ),
                .RES_ALWAYS_ELEMWISE ( RES_ALWAYS_ELEMWISE ),
                .RES_ALWAYS_VREG     ( RES_ALWAYS_VREG     ),
                .MAY_FLUSH           ( MAY_FLUSH           ),
                .MUL_TYPE            ( MUL_TYPE            ),
                .ADDR_ALIGNED        ( ADDR_ALIGNED        ),
                .MAX_WR_ATTEMPTS     ( MAX_WR_ATTEMPTS     ),
                .INIT_STATE_T        ( state_t             ),
                .DONT_CARE_ZERO      ( DONT_CARE_ZERO      )
            ) pipeline (
                .pipe_in_state_i     ( state_init          ),
                .*
            );
        end
        else if (OP_CNT == 3 && RES_CNT == 1) begin
            localparam int unsigned OP_W           [3] = '{FIRST_OP_W, DFLT_OP_W, MASK_OP_W};
            localparam int unsigned OP_STAGE       [3] = '{1, 2, UNPACK_STAGES-1};
            localparam int unsigned OP_SRC         [3] = '{0, 0, VPORT_CNT-1};
            localparam bit [2:0]    OP_ADDR_OFFSET_OP0 = '0;
            localparam bit [2:0]    OP_MASK            = SECOND_OP_MASK ? 3'b110 : 3'b100;
            localparam bit [2:0]    OP_XREG            = FIRST_OP_XREG  ? 3'b001 : '0;
            localparam bit [2:0]    OP_NARROW          = {1'b0, SECOND_OP_NARROW, FIRST_OP_NARROW};
            // if the first operand is always element-wise, then all other operands are optionally
            localparam bit [2:0]    OP_ALLOW_ELEMWISE  = FIRST_OP_ELEMWISE ? 3'b110 : '0;
            localparam bit [2:0]    OP_ALWAYS_ELEMWISE = ~ALL_OP_ELEMWISE  ? {2'b0, FIRST_OP_ELEMWISE} : '1;
            localparam bit [2:0]    OP_HOLD_FLAG       = FIRST_OP_HOLD_FLAG   ? 3'b001 : '0;
            localparam bit [2:0]    OP_ALT_COUNTER     = FIRST_OP_ALT_COUNTER ? 3'b001 : '0;
            localparam bit [2:0]    OP_ALWAYS_VREG     = {1'b0, SECOND_OP_ALWAYS_VREG, FIRST_OP_ALWAYS_VREG};

            localparam int unsigned RES_W           [1] = '{MAX_RES_W};
            localparam bit [0:0]    RES_ALWAYS_VREG     = '0;
            localparam bit [0:0]    RES_MASK            = '0;
            localparam bit [0:0]    RES_XREG            = '0;
            localparam bit [0:0]    RES_NARROW          = FIRST_RES_NARROW;
            localparam bit [0:0]    RES_ALLOW_ELEMWISE  = FIRST_RES_ALLOW_ELEMWISE;
            localparam bit [0:0]    RES_ALWAYS_ELEMWISE = FIRST_RES_ALWAYS_ELEMWISE;

            vproc_pipeline #(
                .VREG_W              ( VREG_W              ),
                .CFG_VL_W            ( CFG_VL_W            ),
                .XIF_ID_W            ( XIF_ID_W            ),
                .XIF_ID_CNT          ( XIF_ID_CNT          ),
                .UNIT                ( UNIT                ),
                .MAX_VPORT_W         ( MAX_VPORT_W         ),
                .MAX_VADDR_W         ( MAX_VADDR_W         ),
                .VPORT_CNT           ( VPORT_CNT           ),
                .VPORT_W             ( VPORT_W             ),
                .VADDR_W             ( VADDR_W             ),
                .VPORT_ADDR_ZERO     ( VPORT_ADDR_ZERO     ),
                .VPORT_BUFFER        ( VPORT_BUFFER        ),
                .MAX_OP_W            ( MAX_OP_W            ),
                .OP_CNT              ( OP_CNT              ),
                .OP_W                ( OP_W                ),
                .OP_STAGE            ( OP_STAGE            ),
                .OP_SRC              ( OP_SRC              ),
                .OP_ADDR_OFFSET_OP0  ( OP_ADDR_OFFSET_OP0  ),
                .OP_MASK             ( OP_MASK             ),
                .OP_XREG             ( OP_XREG             ),
                .OP_NARROW           ( OP_NARROW           ),
                .OP_ALLOW_ELEMWISE   ( OP_ALLOW_ELEMWISE   ),
                .OP_ALWAYS_ELEMWISE  ( OP_ALWAYS_ELEMWISE  ),
                .OP_HOLD_FLAG        ( OP_HOLD_FLAG        ),
                .OP_ALT_COUNTER      ( OP_ALT_COUNTER      ),
                .OP_ALWAYS_VREG      ( OP_ALWAYS_VREG      ),
                .UNPACK_STAGES       ( UNPACK_STAGES       ),
                .MAX_RES_W           ( MAX_RES_W           ),
                .RES_CNT             ( RES_CNT             ),
                .RES_W               ( RES_W               ),
                .RES_MASK            ( RES_MASK            ),
                .RES_XREG            ( RES_XREG            ),
                .RES_NARROW          ( RES_NARROW          ),
                .RES_ALLOW_ELEMWISE  ( RES_ALLOW_ELEMWISE  ),
                .RES_ALWAYS_ELEMWISE ( RES_ALWAYS_ELEMWISE ),
                .RES_ALWAYS_VREG     ( RES_ALWAYS_VREG     ),
                .MAY_FLUSH           ( MAY_FLUSH           ),
                .MUL_TYPE            ( MUL_TYPE            ),
                .ADDR_ALIGNED        ( ADDR_ALIGNED        ),
                .MAX_WR_ATTEMPTS     ( MAX_WR_ATTEMPTS     ),
                .INIT_STATE_T        ( state_t             ),
                .DONT_CARE_ZERO      ( DONT_CARE_ZERO      )
            ) pipeline (
                .pipe_in_state_i     ( state_init          ),
                .*
            );
        end
        else if (OP_CNT == 3 && RES_CNT == 2) begin
            localparam int unsigned OP_W           [3] = '{FIRST_OP_W, DFLT_OP_W, MASK_OP_W};
            localparam int unsigned OP_STAGE       [3] = '{1, 2, UNPACK_STAGES-1};
            localparam int unsigned OP_SRC         [3] = '{0, 0, VPORT_CNT-1};
            localparam bit [2:0]    OP_ADDR_OFFSET_OP0 = '0;
            localparam bit [2:0]    OP_MASK            = SECOND_OP_MASK ? 3'b110 : 3'b100;
            localparam bit [2:0]    OP_XREG            = FIRST_OP_XREG  ? 3'b001 : '0;
            localparam bit [2:0]    OP_NARROW          = {1'b0, SECOND_OP_NARROW, FIRST_OP_NARROW};
            // if the first operand is always element-wise, then all other operands are optionally
            localparam bit [2:0]    OP_ALLOW_ELEMWISE  = FIRST_OP_ELEMWISE ? 3'b110 : '0;
            localparam bit [2:0]    OP_ALWAYS_ELEMWISE = ~ALL_OP_ELEMWISE  ? {2'b0, FIRST_OP_ELEMWISE} : '1;
            localparam bit [2:0]    OP_HOLD_FLAG       = FIRST_OP_HOLD_FLAG   ? 3'b001 : '0;
            localparam bit [2:0]    OP_ALT_COUNTER     = FIRST_OP_ALT_COUNTER ? 3'b001 : '0;
            localparam bit [2:0]    OP_ALWAYS_VREG     = {1'b0, SECOND_OP_ALWAYS_VREG, FIRST_OP_ALWAYS_VREG};

            localparam int unsigned RES_W           [2] = '{MAX_RES_W, MAX_RES_W/8};
            localparam bit [1:0]    RES_ALWAYS_VREG     = '0;
            localparam bit [1:0]    RES_MASK            = 2'b10;
            localparam bit [1:0]    RES_XREG            = '0;
            localparam bit [1:0]    RES_NARROW          = {1'b0, FIRST_RES_NARROW};
            localparam bit [1:0]    RES_ALLOW_ELEMWISE  = {1'b0, FIRST_RES_ALLOW_ELEMWISE};
            localparam bit [1:0]    RES_ALWAYS_ELEMWISE = {1'b0, FIRST_RES_ALWAYS_ELEMWISE};

            vproc_pipeline #(
                .VREG_W              ( VREG_W              ),
                .CFG_VL_W            ( CFG_VL_W            ),
                .XIF_ID_W            ( XIF_ID_W            ),
                .XIF_ID_CNT          ( XIF_ID_CNT          ),
                .UNIT                ( UNIT                ),
                .MAX_VPORT_W         ( MAX_VPORT_W         ),
                .MAX_VADDR_W         ( MAX_VADDR_W         ),
                .VPORT_CNT           ( VPORT_CNT           ),
                .VPORT_W             ( VPORT_W             ),
                .VADDR_W             ( VADDR_W             ),
                .VPORT_ADDR_ZERO     ( VPORT_ADDR_ZERO     ),
                .VPORT_BUFFER        ( VPORT_BUFFER        ),
                .MAX_OP_W            ( MAX_OP_W            ),
                .OP_CNT              ( OP_CNT              ),
                .OP_W                ( OP_W                ),
                .OP_STAGE            ( OP_STAGE            ),
                .OP_SRC              ( OP_SRC              ),
                .OP_ADDR_OFFSET_OP0  ( OP_ADDR_OFFSET_OP0  ),
                .OP_MASK             ( OP_MASK             ),
                .OP_XREG             ( OP_XREG             ),
                .OP_NARROW           ( OP_NARROW           ),
                .OP_ALLOW_ELEMWISE   ( OP_ALLOW_ELEMWISE   ),
                .OP_ALWAYS_ELEMWISE  ( OP_ALWAYS_ELEMWISE  ),
                .OP_HOLD_FLAG        ( OP_HOLD_FLAG        ),
                .OP_ALT_COUNTER      ( OP_ALT_COUNTER      ),
                .OP_ALWAYS_VREG      ( OP_ALWAYS_VREG      ),
                .UNPACK_STAGES       ( UNPACK_STAGES       ),
                .MAX_RES_W           ( MAX_RES_W           ),
                .RES_CNT             ( RES_CNT             ),
                .RES_W               ( RES_W               ),
                .RES_MASK            ( RES_MASK            ),
                .RES_XREG            ( RES_XREG            ),
                .RES_NARROW          ( RES_NARROW          ),
                .RES_ALLOW_ELEMWISE  ( RES_ALLOW_ELEMWISE  ),
                .RES_ALWAYS_ELEMWISE ( RES_ALWAYS_ELEMWISE ),
                .RES_ALWAYS_VREG     ( RES_ALWAYS_VREG     ),
                .MAY_FLUSH           ( MAY_FLUSH           ),
                .MUL_TYPE            ( MUL_TYPE            ),
                .ADDR_ALIGNED        ( ADDR_ALIGNED        ),
                .MAX_WR_ATTEMPTS     ( MAX_WR_ATTEMPTS     ),
                .INIT_STATE_T        ( state_t             ),
                .DONT_CARE_ZERO      ( DONT_CARE_ZERO      )
            ) pipeline (
                .pipe_in_state_i     ( state_init          ),
                .*
            );
        end
        else if (OP_CNT == 4 && RES_CNT == 1) begin
            localparam int unsigned OP_W           [4] = '{FIRST_OP_W, DFLT_OP_W, EXTRA_OP_W, MASK_OP_W};
            localparam int unsigned OP_STAGE       [4] = '{1, 2, UNPACK_STAGES-1, UNPACK_STAGES-1};
            localparam int unsigned OP_SRC         [4] = '{0, 0, VPORT_CNT-2, VPORT_CNT-1};
            localparam bit [3:0]    OP_ADDR_OFFSET_OP0 = EXTRA_OP_ADDR_OFFSET ? 4'b0100 : '0;
            localparam bit [3:0]    OP_MASK            = SECOND_OP_MASK ? 4'b1010 : 4'b1000;
            localparam bit [3:0]    OP_XREG            = FIRST_OP_XREG  ? 4'b0001 : '0;
            localparam bit [3:0]    OP_NARROW          = {2'b0, SECOND_OP_NARROW, FIRST_OP_NARROW};
            // if the first operand is always element-wise, then all other operands are optionally
            localparam bit [3:0]    OP_ALLOW_ELEMWISE  = FIRST_OP_ELEMWISE ? 4'b1110 : '0;
            localparam bit [3:0]    OP_ALWAYS_ELEMWISE = ~ALL_OP_ELEMWISE  ? {3'b0, FIRST_OP_ELEMWISE} : '1;
            localparam bit [3:0]    OP_HOLD_FLAG       = FIRST_OP_HOLD_FLAG   ? 4'b0001 : '0;
            localparam bit [3:0]    OP_ALT_COUNTER     = FIRST_OP_ALT_COUNTER ? 4'b0001 : '0;
            localparam bit [3:0]    OP_ALWAYS_VREG     = {1'b0, EXTRA_OP_ALWAYS_VREG, SECOND_OP_ALWAYS_VREG, FIRST_OP_ALWAYS_VREG};

            localparam int unsigned RES_W           [1] = '{MAX_RES_W};
            localparam bit [0:0]    RES_ALWAYS_VREG     = '0;
            localparam bit [0:0]    RES_MASK            = '0;
            localparam bit [0:0]    RES_XREG            = '0;
            localparam bit [0:0]    RES_NARROW          = FIRST_RES_NARROW;
            localparam bit [0:0]    RES_ALLOW_ELEMWISE  = FIRST_RES_ALLOW_ELEMWISE;
            localparam bit [0:0]    RES_ALWAYS_ELEMWISE = FIRST_RES_ALWAYS_ELEMWISE;

            vproc_pipeline #(
                .VREG_W              ( VREG_W              ),
                .CFG_VL_W            ( CFG_VL_W            ),
                .XIF_ID_W            ( XIF_ID_W            ),
                .XIF_ID_CNT          ( XIF_ID_CNT          ),
                .UNIT                ( UNIT                ),
                .MAX_VPORT_W         ( MAX_VPORT_W         ),
                .MAX_VADDR_W         ( MAX_VADDR_W         ),
                .VPORT_CNT           ( VPORT_CNT           ),
                .VPORT_W             ( VPORT_W             ),
                .VADDR_W             ( VADDR_W             ),
                .VPORT_ADDR_ZERO     ( VPORT_ADDR_ZERO     ),
                .VPORT_BUFFER        ( VPORT_BUFFER        ),
                .MAX_OP_W            ( MAX_OP_W            ),
                .OP_CNT              ( OP_CNT              ),
                .OP_W                ( OP_W                ),
                .OP_STAGE            ( OP_STAGE            ),
                .OP_SRC              ( OP_SRC              ),
                .OP_ADDR_OFFSET_OP0  ( OP_ADDR_OFFSET_OP0  ),
                .OP_MASK             ( OP_MASK             ),
                .OP_XREG             ( OP_XREG             ),
                .OP_NARROW           ( OP_NARROW           ),
                .OP_ALLOW_ELEMWISE   ( OP_ALLOW_ELEMWISE   ),
                .OP_ALWAYS_ELEMWISE  ( OP_ALWAYS_ELEMWISE  ),
                .OP_HOLD_FLAG        ( OP_HOLD_FLAG        ),
                .OP_ALT_COUNTER      ( OP_ALT_COUNTER      ),
                .OP_ALWAYS_VREG      ( OP_ALWAYS_VREG      ),
                .UNPACK_STAGES       ( UNPACK_STAGES       ),
                .MAX_RES_W           ( MAX_RES_W           ),
                .RES_CNT             ( RES_CNT             ),
                .RES_W               ( RES_W               ),
                .RES_MASK            ( RES_MASK            ),
                .RES_XREG            ( RES_XREG            ),
                .RES_NARROW          ( RES_NARROW          ),
                .RES_ALLOW_ELEMWISE  ( RES_ALLOW_ELEMWISE  ),
                .RES_ALWAYS_ELEMWISE ( RES_ALWAYS_ELEMWISE ),
                .RES_ALWAYS_VREG     ( RES_ALWAYS_VREG     ),
                .MAY_FLUSH           ( MAY_FLUSH           ),
                .MUL_TYPE            ( MUL_TYPE            ),
                .ADDR_ALIGNED        ( ADDR_ALIGNED        ),
                .MAX_WR_ATTEMPTS     ( MAX_WR_ATTEMPTS     ),
                .INIT_STATE_T        ( state_t             ),
                .DONT_CARE_ZERO      ( DONT_CARE_ZERO      )
            ) pipeline (
                .pipe_in_state_i     ( state_init          ),
                .*
            );
        end
    endgenerate

endmodule
