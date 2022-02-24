// Copyright TU Wien
// Licensed under the Solderpad Hardware License v2.1, see LICENSE.txt for details
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1


module vproc_pipeline #(
        parameter int unsigned          VREG_W              = 128,  // width in bits of vector registers
        parameter int unsigned          CFG_VL_W            = 7,    // width of VL reg in bits (= log2(VREG_W))
        parameter int unsigned          XIF_ID_W            = 3,    // width in bits of instruction IDs
        parameter int unsigned          XIF_ID_CNT          = 8,    // total count of instruction IDs
        parameter vproc_pkg::op_unit    UNIT                = UNIT_ALU,
        parameter int unsigned          VPORT_CNT           = 1,
        parameter int unsigned          VPORT_W [VPORT_CNT] = '{0},
        parameter int unsigned          VADDR_W [VPORT_CNT] = '{0},
        parameter int unsigned          MAX_OP_W            = 64,
        parameter int unsigned          OP_CNT              = 1,
        parameter int unsigned          OP_W    [OP_CNT   ] = '{0}, // op widths
        parameter int unsigned          OP_STAGE[OP_CNT   ] = '{0}, // op load stage
        parameter int unsigned          OP_SRC  [OP_CNT   ] = '{0}, // op port index
        parameter int unsigned          UNPACK_STAGES       = 0,
        parameter int unsigned          MAX_RES_W           = 64,
        parameter int unsigned          RES_CNT             = 1,
        parameter int unsigned          RES_W   [RES_CNT  ] = '{0},
        parameter vproc_pkg::mul_type   MUL_TYPE            = vproc_pkg::MUL_GENERIC,
        parameter int unsigned          MAX_WR_ATTEMPTS     = 1,    // max required vregfile write attempts
        parameter bit                   DONT_CARE_ZERO      = 1'b0  // initialize don't care values to zero
    )(
        input  logic                    clk_i,
        input  logic                    async_rst_ni,
        input  logic                    sync_rst_ni,

        input  logic [XIF_ID_W-1:0]     id_i,
        input  vproc_pkg::cfg_vsew      vsew_i,
        input  vproc_pkg::cfg_emul      emul_i,
        input  vproc_pkg::cfg_vxrm      vxrm_i,
        input  logic [CFG_VL_W-1:0]     vl_i,
        input  logic                    vl_0_i,

        input  logic                    op_rdy_i,
        output logic                    op_ack_o,

        input  vproc_pkg::op_mode       mode_i,
        input  vproc_pkg::op_widenarrow widenarrow_i,
        input  vproc_pkg::op_regs       rs1_i,
        input  vproc_pkg::op_regs       rs2_i,
        input  logic [4:0]              vd_i,

        input  logic [31:0]             vreg_pend_wr_i,
        output logic [31:0]             vreg_pend_rd_o,
        input  logic [31:0]             vreg_pend_rd_i,

        output logic [31:0]             clear_wr_hazards_o,

        input  logic [XIF_ID_CNT-1:0]   instr_spec_i,
        input  logic [XIF_ID_CNT-1:0]   instr_killed_i,
        output logic                    instr_done_valid_o,
        output logic [XIF_ID_W-1:0]     instr_done_id_o,

        // connections to register file:
        input  logic [VREG_W-1:0]       vreg_mask_i,
        input  logic [VREG_W-1:0]       vreg_rd_i,
        output logic [4:0]              vreg_rd_addr_o,
        input  logic [VREG_W-1:0]       vreg_rd3_i,
        output logic [4:0]              vreg_rd3_addr_o,
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

    if ((MAX_OP_W & (MAX_OP_W - 1)) != 0 || MAX_OP_W < 32 || MAX_OP_W >= VREG_W) begin
        $fatal(1, "The vector pipeline operand width MAX_OP_W must be at least 32, less than ",
                  "the vector register width VREG_W and a power of two.  ",
                  "The current value of %d is invalid.", MAX_OP_W);
    end

    if (MAX_WR_ATTEMPTS < 1 || (1 << (MAX_WR_ATTEMPTS - 1)) > VREG_W / MAX_OP_W) begin
        $fatal(1, "The maximum number of write attempts MAX_WR_ATTEMPTS of a vector pipeline ",
                  "must be at least 1 and 2^(MAX_WR_ATTEMPTS-1) must be less than or ",
                  "equal to the ratio of the vector register width vs the operand width ",
                  "of that unit.  ",
                  "MAX_WR_ATTEMPTS is %d and that ratio is %d.",
                  MAX_WR_ATTEMPTS, VREG_W / MAX_OP_W);
    end

    // max number of cycles by which a write can be delayed
    localparam int unsigned MAX_WR_DELAY = (1 << (MAX_WR_ATTEMPTS - 1)) - 1;


    localparam bit [2:0] VPORT_ADDR_ZERO    = (UNIT == UNIT_MUL) ? 3'b100 : 3'b10;
    localparam bit [2:0] VPORT_BUFFER       = (UNIT == UNIT_MUL) ? 3'b001 : 3'b01;

    localparam bit [3:0] OP_ADDR_OFFSET_OP0 =  (UNIT == UNIT_ELEM) ? 4'b0100 : '0;
    localparam bit [3:0] OP_MASK            =  (UNIT == UNIT_MUL ) ? 4'b1000 : (
                                               (UNIT == UNIT_ELEM) ? 4'b1010 : (
                                               (UNIT == UNIT_SLD ) ? 4'b10   :
                                                                     4'b100
                                              ));
    localparam bit [3:0] OP_XREG            = ((UNIT == UNIT_MUL ) | (UNIT == UNIT_ALU)) ? 4'b0001 : '0;
    localparam bit [3:0] OP_NARROW          = ((UNIT == UNIT_MUL ) | (UNIT == UNIT_ALU)) ? 4'b0011 : (
                                              ( UNIT == UNIT_ELEM                      ) ? 4'b0001 :
                                                                                            '0
                                              );
    localparam bit [3:0] OP_ALLOW_ELEMWISE  =  (UNIT == UNIT_LSU ) ? 4'b110  : '0;
    localparam bit [3:0] OP_ALWAYS_ELEMWISE =  (UNIT == UNIT_LSU ) ? 4'b001  : (
                                               (UNIT == UNIT_ELEM) ? 4'b1111 :
                                                                      '0
                                              );
    localparam bit [3:0] OP_HOLD_FLAG       =  (UNIT == UNIT_ELEM) ? 4'b0001 : '0;


    // Select operands that are always vector registers and always used (avoids check for vreg flag)
    localparam bit [3:0] OP_ALWAYS_VREG = (UNIT == UNIT_SLD) ? 4'b01 : '0;

    localparam bit [3:0] OP_ALT_COUNTER = (UNIT == UNIT_SLD) ? 4'b01 : '0;


    localparam bit [1:0] RES_ALWAYS_VREG     = '0;
    localparam bit [1:0] RES_MASK            = (UNIT == UNIT_ALU ) ? 2'b10 : '0;
    localparam bit [1:0] RES_NARROW          = (UNIT == UNIT_ALU ) ? 2'b01 : '0;
    localparam bit [1:0] RES_ALLOW_ELEMWISE  = (UNIT == UNIT_LSU ) ? 2'b1  : '0;
    localparam bit [1:0] RES_ALWAYS_ELEMWISE = (UNIT == UNIT_ELEM) ? 2'b1  : '0;


    ///////////////////////////////////////////////////////////////////////////
    // STATE LOGIC

    // Smallest operand width.  If element-wise operation may be required the smallest width is
    // always 8 bit (i.e., the smallest element width.
    // TODO this should actually use the minimum operand width, not the maximum.
    localparam int unsigned SMALLEST_OP_W = (
        (OP_ALLOW_ELEMWISE != '0) | (OP_ALWAYS_ELEMWISE != '0)
    ) ? 8 : MAX_OP_W;

    localparam int unsigned CYCLES_PER_VREG = VREG_W / SMALLEST_OP_W;
    localparam int unsigned COUNTER_W       = $clog2(CYCLES_PER_VREG) + 4;

    localparam int unsigned GATHER_CYCLES_PER_VREG = VREG_W / MAX_OP_W;
    localparam int unsigned GATHER_COUNTER_W       = $clog2(GATHER_CYCLES_PER_VREG);

    typedef union packed {
        logic [COUNTER_W-1:0] val;
        struct packed {
            logic                 sign; // sign bit (only used for down slide operations)
            logic [2:0]           mul;  // mul part (vreg index)
            logic [COUNTER_W-5:0] low;  // counter part in vreg (vreg pos)
        } part;
    } counter_t;

    localparam AUX_COUNTER_W = GATHER_COUNTER_W;

    typedef struct packed {
        counter_t                    count;
        counter_t                    alt_count;
        logic                        alt_count_valid;
        count_inc_e                  count_inc;      // counter increment policy
        logic [AUX_COUNTER_W-1:0]    aux_count;
        logic                        first_cycle;
        logic                        last_cycle;
        logic                        requires_flush;
        logic [XIF_ID_W-1:0]         id;
        op_mode                      mode;
        cfg_vsew                     eew;        // effective element width
        cfg_emul                     emul;       // effective MUL factor
        cfg_vxrm                     vxrm;
        logic [CFG_VL_W-1:0]         vl;
        logic                        vl_0;
        logic [$clog2(MAX_OP_W/8)-1:0] vl_part;
        logic                          vl_part_0;
        logic                          last_vl_part;    // last VL part that is not 0
        //op_regs                      rs1;
        logic [31:0]                   xval;


        unpack_flags [OP_CNT-1:0]       op_flags;
        logic        [OP_CNT-1:0]       op_load;
        logic        [OP_CNT-1:0][4 :0] op_vaddr;
        logic        [OP_CNT-1:0][31:0] op_xval;

        logic        [RES_CNT-1:0]      res_vreg;
        logic        [RES_CNT-1:0]      res_narrow;
        logic                           res_store;
        logic                           res_shift;
        logic        [4:0]              res_vaddr;
    } ctrl_t;

    logic        state_valid_q,  state_valid_d;
    ctrl_t       state_q,        state_d;
    logic [31:0] vreg_pend_wr_q, vreg_pend_wr_d; // local copy of global vreg write mask
    logic              last_cycle_q, last_cycle_d;
    logic [OP_CNT-1:0] op_load_q,  op_load_d;
    logic [OP_CNT-1:0] op_shift_q, op_shift_d;
    always_ff @(posedge clk_i or negedge async_rst_ni) begin : vproc_pipeline_state_valid
        if (~async_rst_ni) begin
            state_valid_q <= 1'b0;
        end
        else if (~sync_rst_ni) begin
            state_valid_q <= 1'b0;
        end else begin
            state_valid_q <= state_valid_d;
        end
    end
    always_ff @(posedge clk_i) begin : vproc_pipeline_state
        state_q        <= state_d;
        vreg_pend_wr_q <= vreg_pend_wr_d;
        if (~state_valid_q | pipeline_ready) begin
            last_cycle_q   <= last_cycle_d;
            op_load_q      <= op_load_d;
            op_shift_q     <= op_shift_d;
        end
    end

    // whether the auxiliary counter is used
    logic aux_count_used;
    always_comb begin
        aux_count_used = '0;
        for (int i = 0; i < OP_CNT; i++) begin
            if (OP_ADDR_OFFSET_OP0[i] & (OP_ALWAYS_VREG[i] | state_q.op_flags[i].vreg)) begin
                aux_count_used = 1'b1;
            end
        end
    end

    logic op_reduction;
    always_comb begin
        op_reduction = DONT_CARE_ZERO ? 1'b0 : 1'bx;
        unique case (mode_i.elem.op)
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

    logic pipeline_ready;
    counter_t count_next_inc, alt_count_next_inc;
    always_comb begin
        op_ack_o       = 1'b0;
        state_valid_d  = state_valid_q;
        state_d        = state_q;
        vreg_pend_wr_d = vreg_pend_wr_q & vreg_pend_wr_i;

        if ((~state_valid_q) | (last_cycle_q & pipeline_ready & ((UNIT != UNIT_ELEM) | ~state_q.requires_flush))) begin
            op_ack_o      = 1'b1;
            state_valid_d = op_rdy_i;

            state_d.count = '0;
            if ((UNIT == UNIT_SLD) & (mode_i.sld.dir == SLD_DOWN)) begin
                state_d.count.part.sign = '1;
                state_d.count.part.mul  = '1;
            end

            state_d.alt_count.val = '0;
            if (UNIT == UNIT_SLD) begin
                state_d.alt_count.val = DONT_CARE_ZERO ? '0 : 'x;
                if (mode_i.sld.slide1) begin
                    if (mode_i.sld.dir == SLD_UP) begin
                        // slide counter is all zeroes for up slide, except for a byte slide of 4
                        // when the operand width is 32 bits, then it is 1, since the counter then
                        // captures all but the 2 lowest bits of the byte slide value
                        unique case (vsew_i)
                            VSEW_8,
                            VSEW_16: state_d.alt_count.val = '0;
                            VSEW_32: state_d.alt_count.val = {{COUNTER_W-1{1'b0}}, MAX_OP_W == 32};
                            default: ;
                        endcase
                    end else begin
                        // slide counter is all ones for down slide, even with a byte slide value of
                        // -4 since this has no effect on any but the 2 lowest bits of the byte
                        // slide value
                        state_d.alt_count.val = {4'b1111, {(COUNTER_W-5){1'b0}}, 1'b1};
                    end
                end
                else if (mode_i.sld.dir == SLD_UP) begin
                    unique case (vsew_i)
                        VSEW_8:  state_d.alt_count.val = -{1'b0, rs1_i.r.xval[$clog2(MAX_OP_W/8)   +: COUNTER_W-1]};
                        VSEW_16: state_d.alt_count.val = -{1'b0, rs1_i.r.xval[$clog2(MAX_OP_W/8)-1 +: COUNTER_W-1]};
                        VSEW_32: state_d.alt_count.val = -{1'b0, rs1_i.r.xval[$clog2(MAX_OP_W/8)-2 +: COUNTER_W-1]};
                        default: ;
                    endcase
                end else begin
                    unique case (vsew_i)
                        VSEW_8:  state_d.alt_count.val = ({4'b1111, {(COUNTER_W-4){1'b0}}, {$clog2(MAX_OP_W/8){1'b1}}} + {1'b0, rs1_i.r.xval[$clog2(VREG_W/8)+2:0]      }) >> $clog2(MAX_OP_W/8);
                        VSEW_16: state_d.alt_count.val = ({4'b1111, {(COUNTER_W-4){1'b0}}, {$clog2(MAX_OP_W/8){1'b1}}} + {1'b0, rs1_i.r.xval[$clog2(VREG_W/8)+1:0], 1'b0}) >> $clog2(MAX_OP_W/8);
                        VSEW_32: state_d.alt_count.val = ({4'b1111, {(COUNTER_W-4){1'b0}}, {$clog2(MAX_OP_W/8){1'b1}}} + {1'b0, rs1_i.r.xval[$clog2(VREG_W/8)+0:0], 2'b0}) >> $clog2(MAX_OP_W/8);
                        default: ;
                    endcase
                end
            end

            state_d.count_inc = COUNT_INC_1;
            if ((OP_ALLOW_ELEMWISE != '0) | (OP_ALWAYS_ELEMWISE != '0)) begin
                state_d.count_inc = DONT_CARE_ZERO ? count_inc_e'('0) : count_inc_e'('x);
                unique case ((UNIT == UNIT_LSU) ? mode_i.lsu.eew : vsew_i)
                    VSEW_8:  state_d.count_inc = COUNT_INC_1;
                    VSEW_16: state_d.count_inc = COUNT_INC_2;
                    VSEW_32: state_d.count_inc = COUNT_INC_4;
                    default: ;
                endcase
            end
            if ((UNIT == UNIT_LSU) & (mode_i.lsu.stride == LSU_UNITSTRIDE)) begin
                state_d.count_inc = COUNT_INC_MAX;
            end

            state_d.aux_count      = (mode_i.elem.op == ELEM_VRGATHER) ? '0 : '1;
            state_d.first_cycle    = 1'b1;
            state_d.requires_flush = (UNIT == UNIT_ELEM) & ((mode_i.elem.op == ELEM_VCOMPRESS) | op_reduction);
            state_d.id             = id_i;
            state_d.mode           = mode_i;
            state_d.emul           = emul_i;
            state_d.eew            = (UNIT == UNIT_LSU) ? mode_i.lsu.eew : vsew_i;
            state_d.vxrm           = vxrm_i;
            state_d.vl             = vl_i;
            state_d.vl_0           = vl_0_i;
            state_d.xval           = rs1_i.r.xval;
            if ((UNIT == UNIT_SLD) & ~mode_i.sld.slide1) begin
                // convert element offset to byte offset for the relevant section of rs1 and negate
                // for down slides
                if (mode_i.sld.dir == SLD_UP) begin
                    unique case (vsew_i)
                        VSEW_8:  state_d.xval[$clog2(VREG_W/8)+3:0] =  {1'b0, rs1_i.r.xval[$clog2(VREG_W/8)+2:0]      };
                        VSEW_16: state_d.xval[$clog2(VREG_W/8)+3:0] =  {1'b0, rs1_i.r.xval[$clog2(VREG_W/8)+1:0], 1'b0};
                        VSEW_32: state_d.xval[$clog2(VREG_W/8)+3:0] =  {1'b0, rs1_i.r.xval[$clog2(VREG_W/8)+0:0], 2'b0};
                        default: ;
                    endcase
                end else begin
                    unique case (vsew_i)
                        VSEW_8:  state_d.xval[$clog2(VREG_W/8)+3:0] = -{1'b0, rs1_i.r.xval[$clog2(VREG_W/8)+2:0]      };
                        VSEW_16: state_d.xval[$clog2(VREG_W/8)+3:0] = -{1'b0, rs1_i.r.xval[$clog2(VREG_W/8)+1:0], 1'b0};
                        VSEW_32: state_d.xval[$clog2(VREG_W/8)+3:0] = -{1'b0, rs1_i.r.xval[$clog2(VREG_W/8)+0:0], 2'b0};
                        default: ;
                    endcase
                end
            end
            vreg_pend_wr_d       = vreg_pend_wr_i;


            state_d.op_flags[0]        = unpack_flags'('0);
            state_d.op_flags[1]        = unpack_flags'('0);
            state_d.op_flags[OP_CNT-2] = unpack_flags'('0);
            state_d.op_flags[OP_CNT-1] = unpack_flags'('0);
            if ((UNIT == UNIT_LSU) | (UNIT == UNIT_SLD)) begin
                state_d.op_flags[0].vreg     = rs2_i.vreg;
                state_d.op_vaddr[0]          = rs2_i.r.vaddr;
                state_d.op_xval [0]          = rs2_i.r.xval;
                state_d.op_flags[1].vreg     = mode_i.lsu.store;
                state_d.op_vaddr[1]          = vd_i;
            end else begin
                state_d.op_flags[0].vreg     = ((UNIT == UNIT_ELEM) & ((mode_i.elem.op == ELEM_XMV) | op_reduction)) | rs1_i.vreg;
                state_d.op_flags[0].narrow   = widenarrow_i != OP_SINGLEWIDTH;
                state_d.op_flags[0].sigext   = ((UNIT == UNIT_ALU) & mode_i.alu.sigext) | ((UNIT == UNIT_MUL) & mode_i.mul.op1_signed) | ((UNIT == UNIT_ELEM) & mode_i.elem.sigext);
                //state_d.op_vaddr[0]          = rs1_i.r.vaddr;
                state_d.op_vaddr[0]          = ((UNIT == UNIT_ELEM) & ((mode_i.elem.op == ELEM_XMV) | op_reduction)) ? rs2_i.r.vaddr : rs1_i.r.vaddr;
                state_d.op_xval [0]          = rs1_i.r.xval;
                state_d.op_flags[1].vreg     = rs2_i.vreg;
                state_d.op_flags[1].narrow   = widenarrow_i == OP_WIDENING;
                state_d.op_flags[1].sigext   = ((UNIT == UNIT_ALU) & mode_i.alu.sigext) | ((UNIT == UNIT_MUL) & mode_i.mul.op2_signed);
                //state_d.op_vaddr[1]          = rs2_i.r.vaddr;
                state_d.op_vaddr[1]          = ((UNIT == UNIT_ELEM) & op_reduction) ? rs1_i.r.vaddr : rs2_i.r.vaddr;
                if (UNIT == UNIT_MUL) begin
                    state_d.op_vaddr[1]             = mode_i.mul.op2_is_vd ? vd_i : rs2_i.r.vaddr;
                    state_d.op_flags[OP_CNT-2].vreg = mode_i.mul.op == MUL_VMACC;
                    state_d.op_vaddr[OP_CNT-2]      = mode_i.mul.op2_is_vd ? rs2_i.r.vaddr : vd_i;
                end
                if (UNIT == UNIT_ELEM) begin
                    state_d.op_flags[1].vreg        = (((UNIT == UNIT_ELEM) & op_reduction) | rs2_i.vreg) & (mode_i.elem.op != ELEM_VRGATHER);
                    state_d.op_flags[OP_CNT-2].vreg = mode_i.elem.op == ELEM_VRGATHER;
                    state_d.op_vaddr[OP_CNT-2]      = rs2_i.r.vaddr;
                end
            end
            unique case (UNIT)
                UNIT_LSU:  state_d.op_flags[OP_CNT-1].vreg = mode_i.lsu.masked;
                UNIT_ALU:  state_d.op_flags[OP_CNT-1].vreg = mode_i.alu.op_mask != ALU_MASK_NONE;
                UNIT_MUL:  state_d.op_flags[OP_CNT-1].vreg = mode_i.mul.masked;
                UNIT_SLD:  state_d.op_flags[OP_CNT-1].vreg = mode_i.sld.masked;
                UNIT_ELEM: state_d.op_flags[OP_CNT-1].vreg = mode_i.elem.masked;
                default: ;
            endcase
            state_d.op_flags[OP_CNT-1].elemwise = (UNIT == UNIT_LSU) & (mode_i.lsu.stride != LSU_UNITSTRIDE);

            state_d.res_vreg  [0] = (UNIT != UNIT_LSU) | ~mode_i.lsu.store;
            state_d.res_narrow[0] = (UNIT == UNIT_ALU) ? (widenarrow_i == OP_NARROWING) : '0;
            state_d.res_vaddr     = vd_i;
            if (UNIT == UNIT_ALU) begin
                state_d.res_vreg [0        ] = ~mode_i.alu.cmp;
                state_d.res_vreg [RES_CNT-1] =  mode_i.alu.cmp;
            end
        end
        else if (state_valid_q & pipeline_ready) begin
            state_valid_d        = ~last_cycle_q;
            state_d.first_cycle  = 1'b0;

            state_d.count     = count_next_inc;
            state_d.alt_count = alt_count_next_inc;
            if (aux_count_used) begin
                state_d.aux_count = state_q.aux_count + 1;
            end

            for (int i = 0; i < OP_CNT; i++) begin
                if ((OP_ADDR_OFFSET_OP0 != '0) & ~OP_ADDR_OFFSET_OP0[i]) begin
                    state_d.op_flags[i].hold = state_q.aux_count != '1;
                end
            end

            if (UNIT == UNIT_ELEM) begin
                state_valid_d = ~last_cycle_q | state_q.requires_flush;
                if (last_cycle_q) begin
                    state_d.count.val      = '0;
                    state_d.count.part.mul = '1;
                    state_d.mode.elem.op   = ELEM_FLUSH;
                    state_d.requires_flush = 1'b0;
                    //state_d.rs1.vreg       = 1'b0;
                    for (int i = 0; i < OP_CNT; i++) begin
                        //state_d.op_load [i]      = '0;
                        state_d.op_flags[i].vreg = '0;
                    end
                end
            end
        end
    end

    always_comb begin
        count_next_inc     = state_q.count;
        alt_count_next_inc = state_q.alt_count.val;
        if ((OP_ADDR_OFFSET_OP0 == '0) | (state_q.aux_count == '1)) begin
            unique case (state_q.count_inc)
                COUNT_INC_1: begin
                    count_next_inc.val     = state_q.count.val     + COUNTER_W'(1);
                    alt_count_next_inc.val = state_q.alt_count.val + COUNTER_W'(1);
                end
                COUNT_INC_2: begin
                    count_next_inc.val     = state_q.count.val     + COUNTER_W'(2);
                    alt_count_next_inc.val = state_q.alt_count.val + COUNTER_W'(2);
                end
                COUNT_INC_4: begin
                    count_next_inc.val     = state_q.count.val     + COUNTER_W'(4);
                    alt_count_next_inc.val = state_q.alt_count.val + COUNTER_W'(4);
                end
                COUNT_INC_MAX: begin
                    count_next_inc.val     = state_q.count.val     + (1 << $clog2(MAX_OP_W/SMALLEST_OP_W));
                    alt_count_next_inc.val = state_q.alt_count.val + (1 << $clog2(MAX_OP_W/SMALLEST_OP_W));
                end
                default: ;
            endcase
        end
    end

    always_comb begin
        last_cycle_d = DONT_CARE_ZERO ? 1'b0 : 1'bx;
        // first cycle is not last cycle unless EMUL is 1 and the counter has no low part
        if (op_ack_o) begin
            // TODO take exceptions into account (OP_ALT_COUNTER != 0 and auxiliary counter)
            last_cycle_d = (emul_i == EMUL_1) & (COUNTER_W == 4);
        end else begin
            last_cycle_d = count_next_inc.val[COUNTER_W-5:$clog2(MAX_OP_W/SMALLEST_OP_W)] == '1;
            // clear last cycle in case lower bits are not set for lower counter increments
            unique case (state_q.count_inc)
                COUNT_INC_1: for (int i = 0; i < $clog2(MAX_OP_W/SMALLEST_OP_W); i++) begin
                    last_cycle_d &= count_next_inc.val[i];
                end
                COUNT_INC_2: for (int i = 1; i < $clog2(MAX_OP_W/SMALLEST_OP_W); i++) begin
                    last_cycle_d &= count_next_inc.val[i];
                end
                COUNT_INC_4: for (int i = 2; i < $clog2(MAX_OP_W/SMALLEST_OP_W); i++) begin
                    last_cycle_d &= count_next_inc.val[i];
                end
                default: ;
            endcase
            // clear last cycle based on EMUL
            unique case (state_q.emul)
                EMUL_2: last_cycle_d &= count_next_inc.part.mul[  0] == '1;
                EMUL_4: last_cycle_d &= count_next_inc.part.mul[1:0] == '1;
                EMUL_8: last_cycle_d &= count_next_inc.part.mul[2:0] == '1;
                default: ;
            endcase
            if ((OP_ALT_COUNTER != '0) & state_q.count.part.sign) begin
                last_cycle_d = '0;
            end
            if (aux_count_used & ((state_q.aux_count ^ AUX_COUNTER_W'(1)) != '1)) begin
                last_cycle_d = '0;
            end
        end
    end

    counter_t [OP_CNT-1:0] op_count;
    always_comb begin
        for (int i = 0; i < OP_CNT; i++) begin
            // use next value of counter rather than current (including potential new instruction)
            op_count[i] = OP_ALT_COUNTER[i] ? state_d.alt_count : state_d.count;
        end
    end
    always_comb begin
        op_load_d  = '0;
        op_shift_d = '0;
        for (int i = 0; i < OP_CNT; i++) begin
            if (OP_ADDR_OFFSET_OP0[i]) begin
                if (state_d.aux_count == '0) begin
                    op_load_d[i] = OP_ALWAYS_VREG[i] | state_d.op_flags[i].vreg;
                end
                op_shift_d[i] = 1'b1;
            end
            else if (~aux_count_used | (state_d.aux_count == '0)) begin
                if (~OP_MASK[i]) begin
                    if ((op_count[i].part.low == '0) &
                        (~OP_NARROW[i] | ~state_d.op_flags[i].narrow | ~op_count[i].part.mul[0])
                    ) begin
                        op_load_d[i] = (OP_ALWAYS_VREG[i] | state_d.op_flags[i].vreg) &
                                       ((UNIT != UNIT_ELEM) | ~last_cycle_q); // may need flushing

                        // if the alternative counter is used for some operands the counter's
                        // sign and MUL part might be invalid for the current EMUL, in which
                        // case the load needs to be suppressed
                        if (OP_ALT_COUNTER != '0) begin
                            unique case (state_d.emul)
                                EMUL_1: if (  op_count[i].val[COUNTER_W-1 -: 4]             != '0) begin
                                    op_load_d[i] = '0;
                                end
                                EMUL_2: if (((op_count[i].val[COUNTER_W-1 -: 4]) & 4'b1110) != '0) begin
                                    op_load_d[i] = '0;
                                end
                                EMUL_4: if (((op_count[i].val[COUNTER_W-1 -: 4]) & 4'b1100) != '0) begin
                                    op_load_d[i] = '0;
                                end
                                EMUL_8: if (((op_count[i].val[COUNTER_W-1 -: 4]) & 4'b1000) != '0) begin
                                    op_load_d[i] = '0;
                                end
                                default: ;
                            endcase
                        end
                    end

                    // Operands are shifted after OP_W bits have been consumed.
                    if ((op_count[i].val & ~({COUNTER_W{1'b1}} << $clog2(OP_W[i] / SMALLEST_OP_W))) == '0) begin
                        op_shift_d[i] = ~OP_NARROW[i] | ~state_d.op_flags[i].narrow |
                                        ~op_count[i].val[$clog2(OP_W[i] / SMALLEST_OP_W)];
                    end
                end else begin
                    // Masks are only fetched in the first cycle but never anytime later
                    if (op_count[i].val == '0) begin
                        op_load_d[i] = OP_ALWAYS_VREG[i] | state_d.op_flags[i].vreg;
                    end
                    // The amount of mask bits consumed each cycle depends on the element width
                    if ((op_count[i].val & ~({COUNTER_W{1'b1}} << $clog2(OP_W[i] / (SMALLEST_OP_W / 8)))) == '0) begin
                        op_shift_d[i] = DONT_CARE_ZERO ? '0 : 'x;
                        unique case (state_d.eew)
                            VSEW_8:  op_shift_d[i] = 1'b1;
                            VSEW_16: op_shift_d[i] = op_count[i].val[$clog2(OP_W[i] / (SMALLEST_OP_W / 8))     ] == '0;
                            VSEW_32: op_shift_d[i] = op_count[i].val[$clog2(OP_W[i] / (SMALLEST_OP_W / 8)) +: 2] == '0;
                            default: ;
                        endcase
                    end
                end
            end
        end
    end

    logic res_store;
    logic res_shift;
    always_comb begin
        res_store = '0;
        res_shift = '0;
        // Store uses next counter value (after increment, but not taking into account a potential
        // new instruction) and current state (i.e., also disregarding new instructions)
        // TODO consider the auxiliary counter
        if ((count_next_inc.part.low == '0) & ((OP_ALT_COUNTER == '0) | ~state_q.count.part.sign) &
            ((RES_ALWAYS_VREG | state_q.res_vreg) != '0) // at least one valid vreg
        ) begin
            res_store = ((RES_NARROW & state_q.res_narrow) == '0) | ~count_next_inc.part.mul[0];
        end
        // Shifting is delayed by one cycle compared to the store and hence uses the current counter
        if ((state_q.count.val & ~({COUNTER_W{1'b1}} << $clog2(RES_W[0] / SMALLEST_OP_W))) == '0) begin
            res_shift = ((RES_NARROW & state_d.res_narrow) == '0) |
                        ~state_q.count[$clog2(RES_W[0] / SMALLEST_OP_W)];
        end
    end


    ///////////////////////////////////////////////////////////////////////////
    // FIRST STAGE

    logic  state_init_stall;
    logic  state_init_valid;
    ctrl_t state_init;
    always_comb begin
        state_init_valid      = state_valid_q;
        state_init            = state_q;
        state_init.last_cycle = state_valid_q & last_cycle_q;
        // TODO consider only the relevant counter bits for vl_part (i.e., for element-wise access,
        // the lower counter bits should be ignored for EEW > 8; also, the stride bits should be
        // ignored for LSU operation)
        state_init.vl_part      = (state_q.count.val == state_q.vl[CFG_VL_W-1:$clog2(SMALLEST_OP_W/8)]) ?  state_q.vl[$clog2(MAX_OP_W/8)-1:0] : '1;
        state_init.vl_part_0    = (state_q.count.val >  state_q.vl[CFG_VL_W-1:$clog2(SMALLEST_OP_W/8)]) |  state_q.vl_0;
        state_init.last_vl_part = (state_q.count.val == state_q.vl[CFG_VL_W-1:$clog2(SMALLEST_OP_W/8)]) & ~state_q.vl_0;
        if ((UNIT == UNIT_LSU) & (state_q.mode.lsu.stride == LSU_UNITSTRIDE)) begin
            state_init.vl_part      = (state_q.count.val[COUNTER_W-2:$clog2(MAX_OP_W/8)] == state_q.vl[CFG_VL_W-1:$clog2(MAX_OP_W/8)]) ?  state_q.vl[$clog2(MAX_OP_W/8)-1:0] : '1;
            state_init.vl_part_0    = (state_q.count.val[COUNTER_W-2:$clog2(MAX_OP_W/8)] >  state_q.vl[CFG_VL_W-1:$clog2(MAX_OP_W/8)]) |  state_q.vl_0;
            state_init.last_vl_part = (state_q.count.val[COUNTER_W-2:$clog2(MAX_OP_W/8)] == state_q.vl[CFG_VL_W-1:$clog2(MAX_OP_W/8)]) & ~state_q.vl_0;
        end
        for (int i = 0; i < OP_CNT; i++) begin
            state_init.op_load [i]       = op_load_q [i];
            state_init.op_flags[i].shift = op_shift_q[i];
            if (op_load_q[i] & ~OP_ADDR_OFFSET_OP0[i]) begin
                if (OP_NARROW[i] & state_q.op_flags[i].narrow) begin
                    state_init.op_vaddr[i][1:0] = state_q.op_vaddr[i][1:0] | (OP_ALT_COUNTER[i] ? state_q.alt_count.part.mul[2:1] : state_q.count.part.mul[2:1]);
                end else begin
                    state_init.op_vaddr[i][2:0] = state_q.op_vaddr[i][2:0] | (OP_ALT_COUNTER[i] ? state_q.alt_count.part.mul      : state_q.count.part.mul     );
                end
            end
            if (OP_ALT_COUNTER[i]) begin
                state_init.op_flags[i].vreg = OP_ALWAYS_VREG[i] | state_q.op_flags[i].vreg;
                unique case (state_q.emul)
                    EMUL_1: if (  state_q.alt_count.val[COUNTER_W-1 -: 4]             != '0) begin
                        state_init.op_flags[i].vreg = '0;
                    end
                    EMUL_2: if (((state_q.alt_count.val[COUNTER_W-1 -: 4]) & 4'b1110) != '0) begin
                        state_init.op_flags[i].vreg = '0;
                    end
                    EMUL_4: if (((state_q.alt_count.val[COUNTER_W-1 -: 4]) & 4'b1100) != '0) begin
                        state_init.op_flags[i].vreg = '0;
                    end
                    EMUL_8: if (((state_q.alt_count.val[COUNTER_W-1 -: 4]) & 4'b1000) != '0) begin
                        state_init.op_flags[i].vreg = '0;
                    end
                    default: ;
                endcase
            end
        end
        state_init.res_store = res_store;
        state_init.res_shift = res_shift;
        state_init.res_vaddr = state_q.res_vaddr;
        for (int i = 0; i < RES_CNT; i++) begin
            if ((UNIT != UNIT_ELEM) & ~RES_MASK[i] & (RES_ALWAYS_VREG[i] | state_q.res_vreg[i])) begin
                if (RES_NARROW[i] & state_q.res_narrow[i]) begin
                    state_init.res_vaddr[1:0] = state_q.res_vaddr[1:0] | state_q.count.part.mul[2:1];
                end else begin
                    state_init.res_vaddr[2:0] = state_q.res_vaddr[2:0] | state_q.count.part.mul;
                end
            end
        end

        unique case (state_q.emul)
            EMUL_1: state_init.alt_count_valid =   state_q.alt_count.val[COUNTER_W-1 -: 4]             == '0;
            EMUL_2: state_init.alt_count_valid = ((state_q.alt_count.val[COUNTER_W-1 -: 4]) & 4'b1110) == '0;
            EMUL_4: state_init.alt_count_valid = ((state_q.alt_count.val[COUNTER_W-1 -: 4]) & 4'b1100) == '0;
            EMUL_8: state_init.alt_count_valid = ((state_q.alt_count.val[COUNTER_W-1 -: 4]) & 4'b1000) == '0;
            default: ;
        endcase

        if ((UNIT == UNIT_LSU) & ~state_q.first_cycle) begin
            state_init.xval = DONT_CARE_ZERO ? '0 : 'x;
            unique case (state_q.mode.lsu.stride)
                LSU_STRIDED: state_init.xval = state_q.op_xval[0];
                LSU_INDEXED: state_init.xval = state_q.xval;
                default: ;
            endcase
        end
    end
    logic unpack_ready;
    assign pipeline_ready = unpack_ready & ~state_init_stall;


    logic [31:0] state_init_gather_vregs;
    always_comb begin
        state_init_gather_vregs = '0;
        if (OP_ADDR_OFFSET_OP0 != '0) begin
            state_init_gather_vregs = DONT_CARE_ZERO ? '0 : 'x;
            unique case (state_q.emul)
                EMUL_1: state_init_gather_vregs = 32'h01 <<  state_q.op_vaddr[$clog2(OP_ADDR_OFFSET_OP0)];
                EMUL_2: state_init_gather_vregs = 32'h03 << {state_q.op_vaddr[$clog2(OP_ADDR_OFFSET_OP0)][4:1], 1'b0};
                EMUL_4: state_init_gather_vregs = 32'h0F << {state_q.op_vaddr[$clog2(OP_ADDR_OFFSET_OP0)][4:2], 2'b0};
                EMUL_8: state_init_gather_vregs = 32'hFF << {state_q.op_vaddr[$clog2(OP_ADDR_OFFSET_OP0)][4:3], 3'b0};
                default: ;
            endcase
        end
    end

    logic [31:0] pending_gather_vreg_reads_q, pending_gather_vreg_reads_d;
    logic        pending_gather_vreg_reads_clear;
    always_ff @(posedge clk_i or negedge async_rst_ni) begin
        if (~async_rst_ni) begin
            pending_gather_vreg_reads_q <= '0;
        end
        else if (~sync_rst_ni) begin
            pending_gather_vreg_reads_q <= '0;
        end
        else begin
            pending_gather_vreg_reads_q <= pending_gather_vreg_reads_d;
        end
    end
    always_comb begin
        pending_gather_vreg_reads_d = pending_gather_vreg_reads_q;
        if (pending_gather_vreg_reads_clear) begin
            pending_gather_vreg_reads_d = '0;
        end
        if (state_init_valid & ~state_init_stall & (state_init.mode.elem.op == ELEM_VRGATHER)) begin
            pending_gather_vreg_reads_d |= state_init_gather_vregs;
        end
    end


    // Stall vreg reads until pending writes are complete; note that vreg read
    // stalling always happens in the init stage, since otherwise a substantial
    // amount of state would have to be forwarded (such as vreg_pend_wr_q)
    always_comb begin
        state_init_stall = '0;
        for (int i = 0; i < OP_CNT; i++) begin
            if (OP_ADDR_OFFSET_OP0[i]) begin
                state_init_stall |= state_init.op_load[i] & ((state_init_gather_vregs & vreg_pend_wr_q) != '0);
            end else begin
                state_init_stall |= state_init.op_load[i] & vreg_pend_wr_q[VPORT_ADDR_ZERO[OP_SRC[i]] ? '0 : state_init.op_vaddr[i]];
            end
        end
    end

    logic [OP_CNT-1:0][31:0] op_pend_reads;
    generate
        for (genvar i = 0; i < OP_CNT; i++) begin
            always_comb begin
                op_pend_reads[i] = '0;
                if (OP_ADDR_OFFSET_OP0[i]) begin
                    if (OP_ALWAYS_VREG[i] | state_q.op_flags[i].vreg) begin
                        op_pend_reads[i] = pending_gather_vreg_reads_q;
                    end
                end
                else if (OP_MASK[i]) begin
                    if ((OP_ALT_COUNTER != '0) & (OP_ALT_COUNTER[i] ? state_q.alt_count.part.sign : state_q.count.part.sign) & (OP_ALWAYS_VREG[i] | state_q.op_flags[i].vreg)) begin
                        op_pend_reads[i] = VPORT_ADDR_ZERO[OP_SRC[i]] ? '0 : (32'b1 << state_q.op_vaddr[i]);
                    end
                end
                // TODO guard with VPORT_ADDR_ZERO[OP_SRC[i]]
                else if (OP_ALT_COUNTER[i]) begin
                    //if (OP_ALWAYS_VREG[i] | state_q.op_flags[i].vreg) begin
                        op_pend_reads[i] = DONT_CARE_ZERO ? '0 : 'x;
                        unique case ({state_q.emul, OP_NARROW[i] & state_q.op_flags[i].narrow})
                            {EMUL_1, 1'b1},
                            {EMUL_1, 1'b0},
                            {EMUL_2, 1'b1}: op_pend_reads[i] = 32'h01 <<  state_q.op_vaddr[i];
                            {EMUL_2, 1'b0},
                            {EMUL_4, 1'b1}: op_pend_reads[i] = 32'h03 << {state_q.op_vaddr[i][4:1], 1'b0};
                            {EMUL_4, 1'b0},
                            {EMUL_8, 1'b1}: op_pend_reads[i] = 32'h0F << {state_q.op_vaddr[i][4:2], 2'b0};
                            {EMUL_8, 1'b0}: op_pend_reads[i] = 32'hFF << {state_q.op_vaddr[i][4:3], 3'b0};
                            default: ;
                        endcase
                    //end
                end
                //else if (OP_ALT_COUNTER != '0) begin
                //end
                else begin
                    if (OP_ALWAYS_VREG[i] | state_q.op_flags[i].vreg) begin
                        op_pend_reads[i] = DONT_CARE_ZERO ? '0 : 'x;
                        unique case ({state_q.emul, OP_NARROW[i] & state_q.op_flags[i].narrow})
                            {EMUL_1, 1'b1},
                            {EMUL_1, 1'b0},
                            {EMUL_2, 1'b1}: op_pend_reads[i] = '0;
                            {EMUL_2, 1'b0}: op_pend_reads[i] = (32'h03 & (32'h02 << state_q.count.part.mul[2:0])) << {state_q.op_vaddr[i][4:1], 1'b0};
                            {EMUL_4, 1'b1}: op_pend_reads[i] = (32'h03 & (32'h02 << state_q.count.part.mul[2:1])) << {state_q.op_vaddr[i][4:1], 1'b0};
                            {EMUL_4, 1'b0}: op_pend_reads[i] = (32'h0F & (32'h0E << state_q.count.part.mul[2:0])) << {state_q.op_vaddr[i][4:2], 2'b0};
                            {EMUL_8, 1'b1}: op_pend_reads[i] = (32'h0F & (32'h0E << state_q.count.part.mul[2:1])) << {state_q.op_vaddr[i][4:2], 2'b0};
                            {EMUL_8, 1'b0}: op_pend_reads[i] = (32'hFF & (32'hFE << state_q.count.part.mul[2:0])) << {state_q.op_vaddr[i][4:3], 3'b0};
                            default: ;
                        endcase
                    end
                end
            end
        end
    endgenerate
    logic [31:0] op_pend_reads_all;
    always_comb begin
        op_pend_reads_all = '0;
        for (int i = 0; i < OP_CNT; i++) begin
            op_pend_reads_all |= op_pend_reads[i];
            if (state_init.op_load[i]) begin
                if (OP_ADDR_OFFSET_OP0[i]) begin
                    op_pend_reads_all |= state_init_gather_vregs;
                end else begin
                    op_pend_reads_all[VPORT_ADDR_ZERO[OP_SRC[i]] ? '0 : state_init.op_vaddr[i]] = 1'b1;
                end
            end
        end
    end

    logic [31:0] unpack_pend_rd;
    assign vreg_pend_rd_o = state_init_valid ? ((op_pend_reads_all & ~vreg_pend_wr_q) | unpack_pend_rd) : '0;

    ctrl_t unpack_flags_all, unpack_flags_any;
    logic  lsu_pending_load, lsu_pending_store;
    assign pending_load_o  = (UNIT == UNIT_LSU) & (
                                 (state_init_valid & ~state_init.mode.lsu.store) |
                                 ~unpack_flags_all.mode.lsu.store | lsu_pending_load
                             );
    assign pending_store_o = (UNIT == UNIT_LSU) & (
                                 (state_init_valid &  state_init.mode.lsu.store) |
                                  unpack_flags_any.mode.lsu.store | lsu_pending_store
                             );


    ///////////////////////////////////////////////////////////////////////////
    // REGISTER READ/WRITE AND UNIT INSTANTIATION

    logic [VPORT_CNT-1:0][4:0]          unpack_vreg_addr;
    logic [VPORT_CNT-1:0][VREG_W  -1:0] unpack_vreg_data;
    logic                               unpack_out_valid;
    logic                               unpack_out_ready;
    ctrl_t                              unpack_out_ctrl;
    logic [OP_CNT   -1:0][MAX_OP_W-1:0] unpack_out_ops;
    vproc_vregunpack #(
        .MAX_VPORT_W          ( VREG_W                                ),
        .MAX_VADDR_W          ( 5                                     ),
        .VPORT_CNT            ( VPORT_CNT                             ),
        .VPORT_W              ( VPORT_W                               ),
        .VADDR_W              ( VADDR_W                               ),
        .VPORT_ADDR_ZERO      ( VPORT_ADDR_ZERO[VPORT_CNT-1:0]        ),
        .VPORT_BUFFER         ( VPORT_BUFFER   [VPORT_CNT-1:0]        ),
        .MAX_OP_W             ( MAX_OP_W                              ),
        .OP_CNT               ( OP_CNT                                ),
        .OP_W                 ( OP_W                                  ),
        .OP_STAGE             ( OP_STAGE                              ),
        .OP_SRC               ( OP_SRC                                ),
        .OP_ADDR_OFFSET_OP0   ( OP_ADDR_OFFSET_OP0[OP_CNT-1:0]        ),
        .OP_MASK              ( OP_MASK           [OP_CNT-1:0]        ),
        .OP_XREG              ( OP_XREG           [OP_CNT-1:0]        ),
        .OP_NARROW            ( OP_NARROW         [OP_CNT-1:0]        ),
        .OP_ALLOW_ELEMWISE    ( OP_ALLOW_ELEMWISE [OP_CNT-1:0]        ),
        .OP_ALWAYS_ELEMWISE   ( OP_ALWAYS_ELEMWISE[OP_CNT-1:0]        ),
        .OP_HOLD_FLAG         ( OP_HOLD_FLAG      [OP_CNT-1:0]        ),
        .UNPACK_STAGES        ( UNPACK_STAGES                         ),
        .FLAGS_T              ( unpack_flags                          ),
        .CTRL_DATA_W          ( $bits(ctrl_t)                         ),
        .DONT_CARE_ZERO       ( DONT_CARE_ZERO                        )
    ) unpack (
        .clk_i                ( clk_i                                 ),
        .async_rst_ni         ( async_rst_ni                          ),
        .sync_rst_ni          ( sync_rst_ni                           ),
        .vreg_rd_addr_o       ( unpack_vreg_addr                      ),
        .vreg_rd_data_i       ( unpack_vreg_data                      ),
        .pipe_in_valid_i      ( state_init_valid & ~state_init_stall  ),
        .pipe_in_ready_o      ( unpack_ready                          ),
        .pipe_in_ctrl_i       ( state_init                            ),
        .pipe_in_eew_i        ( state_init.eew                        ),
        .pipe_in_op_load_i    ( state_init.op_load                    ),
        .pipe_in_op_vaddr_i   ( state_init.op_vaddr                   ),
        .pipe_in_op_flags_i   ( state_init.op_flags                   ),
        .pipe_in_op_xval_i    ( state_init.op_xval                    ),
        .pipe_out_valid_o     ( unpack_out_valid                      ),
        .pipe_out_ready_i     ( unpack_out_ready                      ),
        .pipe_out_ctrl_o      ( unpack_out_ctrl                       ),
        .pipe_out_op_data_o   ( unpack_out_ops                        ),
        .pending_vreg_reads_o ( unpack_pend_rd                        ),
        .stage_valid_any_o    (                                       ),
        .ctrl_flags_any_o     ( unpack_flags_any                      ),
        .ctrl_flags_all_o     ( unpack_flags_all                      )
    );
    assign vreg_rd_addr_o  = unpack_vreg_addr[0];
    assign vreg_rd3_addr_o = unpack_vreg_addr[1];
    generate
        if (UNIT == UNIT_MUL) begin
            always_comb begin
                unpack_vreg_data[0] = vreg_rd_i;
                unpack_vreg_data[1] = vreg_rd3_i;
                unpack_vreg_data[2] = vreg_mask_i;
            end
        end else begin
            always_comb begin
                unpack_vreg_data[0] = vreg_rd_i;
                unpack_vreg_data[1] = vreg_mask_i;
            end
        end
    endgenerate

    assign pending_gather_vreg_reads_clear = (UNIT == UNIT_ELEM) & unpack_out_valid & unpack_out_ctrl.last_cycle;

    logic                  lsu_instr_done_valid;
    logic [XIF_ID_W  -1:0] lsu_instr_done_id;

    logic                                   unit_out_valid;
    logic                                   unit_out_ready;
    ctrl_t                                  unit_out_ctrl;
    logic                                   unit_out_instr_done;
    logic      [RES_CNT-1:0]                pack_res_store, pack_res_valid;
    pack_flags [RES_CNT-1:0]                pack_res_flags;
    logic      [RES_CNT-1:0][MAX_RES_W-1:0] pack_res_data, pack_res_mask;
    logic                                   pack_pend_clear;
    logic      [1:0]                        pack_pend_clear_cnt;
    generate
        if (UNIT == UNIT_LSU) begin
            logic [MAX_OP_W  -1:0] unit_out_res;
            logic [MAX_OP_W/8-1:0] unit_out_mask;
            vproc_lsu #(
                .VMEM_W                   ( MAX_OP_W                          ),
                .CTRL_T                   ( ctrl_t                            ),
                .XIF_ID_W                 ( XIF_ID_W                          ),
                .XIF_ID_CNT               ( XIF_ID_CNT                        ),
                .DONT_CARE_ZERO           ( DONT_CARE_ZERO                    )
            ) lsu (
                .clk_i                    ( clk_i                             ),
                .async_rst_ni             ( async_rst_ni                      ),
                .sync_rst_ni              ( sync_rst_ni                       ),
                .pipe_in_valid_i          ( unpack_out_valid                  ),
                .pipe_in_ready_o          ( unpack_out_ready                  ),
                .pipe_in_ctrl_i           ( unpack_out_ctrl                   ),
                .pipe_in_op1_i            ( unpack_out_ops[0][31:0]           ),
                .pipe_in_op2_i            ( unpack_out_ops[1]                 ),
                .pipe_in_mask_i           ( unpack_out_ops[2][MAX_OP_W/8-1:0] ),
                .pipe_out_valid_o         ( unit_out_valid                    ),
                .pipe_out_ready_i         ( 1'b1                              ),
                .pipe_out_ctrl_o          ( unit_out_ctrl                     ),
                .pipe_out_pend_clr_o      ( pack_pend_clear                   ),
                .pipe_out_res_o           ( unit_out_res                      ),
                .pipe_out_mask_o          ( unit_out_mask                     ),
                .pending_load_o           ( lsu_pending_load                  ),
                .pending_store_o          ( lsu_pending_store                 ),
                .vreg_pend_rd_i           ( vreg_pend_rd_i                    ),
                .instr_spec_i             ( instr_spec_i                      ),
                .instr_killed_i           ( instr_killed_i                    ),
                .instr_done_valid_o       ( lsu_instr_done_valid              ),
                .instr_done_id_o          ( lsu_instr_done_id                 ),
                .trans_complete_valid_o   ( trans_complete_valid_o            ),
                .trans_complete_id_o      ( trans_complete_id_o               ),
                .trans_complete_exc_o     ( trans_complete_exc_o              ),
                .trans_complete_exccode_o ( trans_complete_exccode_o          ),
                .xif_mem_if               ( xif_mem_if                        ),
                .xif_memres_if            ( xif_memres_if                     )
            );
            always_comb begin
                pack_res_data = '0;
                pack_res_mask = '0;

                pack_res_flags[0]                 = pack_flags'('0);
                pack_res_flags[0].shift           = unit_out_ctrl.res_shift;
                pack_res_flags[0].elemwise        = unit_out_ctrl.mode.lsu.stride != LSU_UNITSTRIDE;
                pack_res_store[0]                 = unit_out_ctrl.res_store;
                pack_res_valid[0]                 = unit_out_valid;
                pack_res_data [0]                 = unit_out_res;
                pack_res_mask [0][MAX_OP_W/8-1:0] = unit_out_mask;
            end
            assign pack_pend_clear_cnt = '0;
            assign unit_out_instr_done = unit_out_ctrl.last_cycle;
        end
        else if (UNIT == UNIT_ALU) begin
            logic [MAX_OP_W  -1:0] unit_out_res_alu;
            logic [MAX_OP_W/8-1:0] unit_out_res_cmp;
            logic [MAX_OP_W/8-1:0] unit_out_mask;
            vproc_alu #(
                .ALU_OP_W           ( MAX_OP_W                          ),
                .CTRL_T             ( ctrl_t                            ),
                .DONT_CARE_ZERO     ( DONT_CARE_ZERO                    )
            ) alu (
                .clk_i              ( clk_i                             ),
                .async_rst_ni       ( async_rst_ni                      ),
                .sync_rst_ni        ( sync_rst_ni                       ),
                .pipe_in_valid_i    ( unpack_out_valid                  ),
                .pipe_in_ready_o    ( unpack_out_ready                  ),
                .pipe_in_ctrl_i     ( unpack_out_ctrl                   ),
                .pipe_in_op1_i      ( unpack_out_ops[0]                 ),
                .pipe_in_op2_i      ( unpack_out_ops[1]                 ),
                .pipe_in_mask_i     ( unpack_out_ops[2][MAX_OP_W/8-1:0] ),
                .pipe_out_valid_o   ( unit_out_valid                    ),
                .pipe_out_ready_i   ( unit_out_ready                    ),
                .pipe_out_ctrl_o    ( unit_out_ctrl                     ),
                .pipe_out_res_alu_o ( unit_out_res_alu                  ),
                .pipe_out_res_cmp_o ( unit_out_res_cmp                  ),
                .pipe_out_mask_o    ( unit_out_mask                     )
            );
            always_comb begin
                pack_res_data = '0;
                pack_res_mask = '0;

                pack_res_flags[0]                 = pack_flags'('0);
                pack_res_store[0]                 = unit_out_ctrl.res_store & ~unit_out_ctrl.mode.alu.cmp;
                pack_res_flags[0].shift           = unit_out_ctrl.res_shift;
                pack_res_flags[0].narrow          = unit_out_ctrl.res_narrow[0];
                pack_res_flags[0].saturate        = unit_out_ctrl.mode.alu.sat_res;
                pack_res_flags[0].sig             = unit_out_ctrl.mode.alu.sigext;
                pack_res_valid[0]                 = unit_out_valid;
                pack_res_data [0]                 = unit_out_res_alu;
                pack_res_mask [0][MAX_OP_W/8-1:0] = unit_out_mask;

                pack_res_flags[1]                 = pack_flags'('0);
                pack_res_flags[1].mul_idx         = unit_out_ctrl.count.part.mul;
                pack_res_store[1]                 = unit_out_ctrl.res_store & unit_out_ctrl.mode.alu.cmp;
                pack_res_valid[1]                 = unit_out_valid;
                pack_res_data [1][MAX_OP_W/8-1:0] = unit_out_res_cmp;
                pack_res_mask [1][MAX_OP_W/8-1:0] = unit_out_mask;
            end
            assign pack_pend_clear     = unit_out_ctrl.mode.alu.cmp ? unit_out_ctrl.last_cycle : unit_out_ctrl.res_store;
            assign pack_pend_clear_cnt = '0;
            assign unit_out_instr_done = unit_out_ctrl.last_cycle;
        end
        else if (UNIT == UNIT_MUL) begin
            logic [MAX_OP_W  -1:0] unit_out_res;
            logic [MAX_OP_W/8-1:0] unit_out_mask;
            vproc_mul #(
                .MUL_OP_W         ( MAX_OP_W                          ),
                .MUL_TYPE         ( MUL_TYPE                          ),
                .CTRL_T           ( ctrl_t                            ),
                .DONT_CARE_ZERO   ( DONT_CARE_ZERO                    )
            ) mul (
                .clk_i            ( clk_i                             ),
                .async_rst_ni     ( async_rst_ni                      ),
                .sync_rst_ni      ( sync_rst_ni                       ),
                .pipe_in_valid_i  ( unpack_out_valid                  ),
                .pipe_in_ready_o  ( unpack_out_ready                  ),
                .pipe_in_ctrl_i   ( unpack_out_ctrl                   ),
                .pipe_in_op1_i    ( unpack_out_ops[0]                 ),
                .pipe_in_op2_i    ( unpack_out_ops[1]                 ),
                .pipe_in_op3_i    ( unpack_out_ops[2]                 ),
                .pipe_in_mask_i   ( unpack_out_ops[3][MAX_OP_W/8-1:0] ),
                .pipe_out_valid_o ( unit_out_valid                    ),
                .pipe_out_ready_i ( unit_out_ready                    ),
                .pipe_out_ctrl_o  ( unit_out_ctrl                     ),
                .pipe_out_res_o   ( unit_out_res                      ),
                .pipe_out_mask_o  ( unit_out_mask                     )
            );
            always_comb begin
                pack_res_data = '0;
                pack_res_mask = '0;

                pack_res_flags[0]                 = pack_flags'('0);
                pack_res_store[0]                 = unit_out_ctrl.res_store;
                pack_res_valid[0]                 = unit_out_valid;
                pack_res_data [0]                 = unit_out_res;
                pack_res_mask [0][MAX_OP_W/8-1:0] = unit_out_mask;
            end
            assign pack_pend_clear     = unit_out_ctrl.res_store;
            assign pack_pend_clear_cnt = '0;
            assign unit_out_instr_done = unit_out_ctrl.last_cycle;
        end
        else if (UNIT == UNIT_SLD) begin
            logic [MAX_OP_W  -1:0] unit_out_res;
            logic [MAX_OP_W/8-1:0] unit_out_mask;
            vproc_sld #(
                .SLD_OP_W         ( MAX_OP_W                          ),
                .CTRL_T           ( ctrl_t                            ),
                .DONT_CARE_ZERO   ( DONT_CARE_ZERO                    )
            ) sld (
                .clk_i            ( clk_i                             ),
                .async_rst_ni     ( async_rst_ni                      ),
                .sync_rst_ni      ( sync_rst_ni                       ),
                .pipe_in_valid_i  ( unpack_out_valid                  ),
                .pipe_in_ready_o  ( unpack_out_ready                  ),
                .pipe_in_ctrl_i   ( unpack_out_ctrl                   ),
                .pipe_in_op_i     ( unpack_out_ops[0]                 ),
                .pipe_in_mask_i   ( unpack_out_ops[1][MAX_OP_W/8-1:0] ),
                .pipe_out_valid_o ( unit_out_valid                    ),
                .pipe_out_ready_i ( unit_out_ready                    ),
                .pipe_out_ctrl_o  ( unit_out_ctrl                     ),
                .pipe_out_res_o   ( unit_out_res                      ),
                .pipe_out_mask_o  ( unit_out_mask                     )
            );
            always_comb begin
                pack_res_data = '0;
                pack_res_mask = '0;
                pack_res_flags[0]                 = pack_flags'('0);
                pack_res_store[0]                 = unit_out_ctrl.res_store;
                pack_res_valid[0]                 = unit_out_valid;
                pack_res_data [0]                 = unit_out_res;
                pack_res_mask [0][MAX_OP_W/8-1:0] = unit_out_mask;
            end
            assign pack_pend_clear     = unit_out_ctrl.res_store;
            assign pack_pend_clear_cnt = '0;
            assign unit_out_instr_done = unit_out_ctrl.last_cycle;
        end
        else if (UNIT == UNIT_ELEM) begin
            logic        elem_out_valid;
            logic        elem_out_ready;
            ctrl_t       elem_out_ctrl;
            logic        elem_out_xreg_valid;
            logic        unit_out_stall;
            logic        unit_out_res_valid;
            logic [31:0] unit_out_res;
            logic [3 :0] unit_out_mask;
            vproc_elem #(
                .VREG_W                ( VREG_W                  ),
                .GATHER_OP_W           ( MAX_OP_W                ),
                .CTRL_T                ( ctrl_t                  ),
                .DONT_CARE_ZERO        ( DONT_CARE_ZERO          )
            ) elem (
                .clk_i                 ( clk_i                   ),
                .async_rst_ni          ( async_rst_ni            ),
                .sync_rst_ni           ( sync_rst_ni             ),
                .pipe_in_valid_i       ( unpack_out_valid        ),
                .pipe_in_ready_o       ( unpack_out_ready        ),
                .pipe_in_ctrl_i        ( unpack_out_ctrl         ),
                .pipe_in_op1_i         ( unpack_out_ops[0][31:0] ),
                .pipe_in_op2_i         ( unpack_out_ops[1][31:0] ),
                .pipe_in_op_gather_i   ( unpack_out_ops[2]       ),
                .pipe_in_mask_i        ( unpack_out_ops[3][0]    ),
                .pipe_out_valid_o      ( elem_out_valid          ),
                .pipe_out_ready_i      ( elem_out_ready          ),
                .pipe_out_ctrl_o       ( elem_out_ctrl           ),
                .pipe_out_xreg_valid_o ( elem_out_xreg_valid     ),
                .pipe_out_xreg_data_o  ( xreg_data_o             ),
                .pipe_out_xreg_addr_o  ( xreg_addr_o             ),
                .pipe_out_res_valid_o  ( unit_out_res_valid      ),
                .pipe_out_res_o        ( unit_out_res            ),
                .pipe_out_mask_o       ( unit_out_mask           )
            );
            logic     has_valid_result_q, has_valid_result_d;
            counter_t vd_count_q,         vd_count_d;
            always_ff @(posedge clk_i) begin
                if (elem_out_ready) begin
                    vd_count_q         <= vd_count_d;
                    has_valid_result_q <= has_valid_result_d;
                end
            end
            // track whether there are any valid results
            always_comb begin
                has_valid_result_d = has_valid_result_q;
                if (elem_out_ctrl.first_cycle) begin
                    has_valid_result_d = 1'b0;
                end
                if (unit_out_res_valid) begin
                    has_valid_result_d = 1'b1;
                end
            end
            // determine when we see the first valid result
            logic first_valid_result;
            assign first_valid_result = unit_out_res_valid & (elem_out_ctrl.first_cycle | ~has_valid_result_q);
            always_comb begin
                vd_count_d.val = DONT_CARE_ZERO ? '0 : 'x;
                unique case (elem_out_ctrl.eew)
                    VSEW_8:  vd_count_d.val = vd_count_q.val + {{(COUNTER_W-1){1'b0}}, unit_out_res_valid      };
                    VSEW_16: vd_count_d.val = vd_count_q.val + {{(COUNTER_W-2){1'b0}}, unit_out_res_valid, 1'b0};
                    VSEW_32: vd_count_d.val = vd_count_q.val + {{(COUNTER_W-3){1'b0}}, unit_out_res_valid, 2'b0};
                    default: ;
                endcase
                if (first_valid_result) begin
                    vd_count_d.val      = '0;
                    vd_count_d.val[1:0] = DONT_CARE_ZERO ? '0 : 'x;
                    unique case (elem_out_ctrl.eew)
                        VSEW_8:  vd_count_d.val[1:0] = 2'b00;
                        VSEW_16: vd_count_d.val[1:0] = 2'b01;
                        VSEW_32: vd_count_d.val[1:0] = 2'b11;
                        default: ;
                    endcase
                end
            end
            always_comb begin
                unit_out_ctrl           = elem_out_ctrl;
                unit_out_ctrl.res_store = ~elem_out_ctrl.mode.elem.xreg & unit_out_res_valid & (vd_count_d.part.low == '1);
                unit_out_ctrl.res_vaddr = DONT_CARE_ZERO ? '0 : 'x;
                unique case (elem_out_ctrl.emul)
                    EMUL_1: unit_out_ctrl.res_vaddr = elem_out_ctrl.res_vaddr;
                    EMUL_2: unit_out_ctrl.res_vaddr = elem_out_ctrl.res_vaddr | {4'b0, vd_count_d.part.mul[0:0]};
                    EMUL_4: unit_out_ctrl.res_vaddr = elem_out_ctrl.res_vaddr | {3'b0, vd_count_d.part.mul[1:0]};
                    EMUL_8: unit_out_ctrl.res_vaddr = elem_out_ctrl.res_vaddr | {2'b0, vd_count_d.part.mul[2:0]};
                    default: ;
                endcase
            end
            assign unit_out_stall =                  elem_out_xreg_valid &                    instr_spec_i  [unit_out_ctrl.id];
            assign xreg_valid_o   = elem_out_valid & elem_out_xreg_valid & ~unit_out_stall & ~instr_killed_i[unit_out_ctrl.id];
            assign xreg_id_o      = unit_out_ctrl.id;
            assign unit_out_valid = elem_out_valid &                       ~unit_out_stall;
            assign elem_out_ready = unit_out_ready &                       ~unit_out_stall;
            always_comb begin
                pack_res_data = '0;
                pack_res_mask = '0;
                pack_res_flags[0]       = pack_flags'('0);
                pack_res_flags[0].shift = DONT_CARE_ZERO ? '0 : 'x;
                unique case (unit_out_ctrl.eew)
                    VSEW_8:  pack_res_flags[0].shift = vd_count_d.val[1:0] == '0;
                    VSEW_16: pack_res_flags[0].shift = vd_count_d.val[1:1] == '0;
                    VSEW_32: pack_res_flags[0].shift = 1'b1;
                    default: ;
                endcase
                pack_res_store[0]      = unit_out_ctrl.res_store;
                pack_res_valid[0]      = unit_out_res_valid;
                pack_res_data [0]      = unit_out_res;
                pack_res_mask [0][3:0] = unit_out_mask;
            end
            assign pack_pend_clear     = unit_out_ctrl.last_cycle & ~unit_out_ctrl.requires_flush & ~unit_out_ctrl.mode.elem.xreg;
            assign pack_pend_clear_cnt = unit_out_ctrl.emul; // TODO reductions always have destination EMUL == 1
            assign unit_out_instr_done = unit_out_ctrl.last_cycle & ~unit_out_ctrl.requires_flush;
        end
    endgenerate


    logic [31          :0] pack_pending_vreg_reads;
    logic [XIF_ID_CNT-1:0] pack_instr_spec;
    logic [XIF_ID_CNT-1:0] pack_instr_killed;
    logic                  pack_instr_done_valid;
    logic [XIF_ID_W  -1:0] pack_instr_done_id;
    assign pack_pending_vreg_reads = (UNIT != UNIT_LSU) ? vreg_pend_rd_i : '0;
    assign pack_instr_spec         = (UNIT != UNIT_LSU) ? instr_spec_i   : '0;
    assign pack_instr_killed       = (UNIT != UNIT_LSU) ? instr_killed_i : '0;
    assign instr_done_valid_o      = (UNIT != UNIT_LSU) ? pack_instr_done_valid : lsu_instr_done_valid;
    assign instr_done_id_o         = (UNIT != UNIT_LSU) ? pack_instr_done_id    : lsu_instr_done_id;

    vproc_vregpack #(
        .VPORT_W                     ( VREG_W                            ),
        .VADDR_W                     ( 5                                 ),
        .VPORT_WR_ATTEMPTS           ( MAX_WR_ATTEMPTS                   ),
        .VPORT_PEND_CLR_BULK         ( UNIT == UNIT_ELEM                 ),
        .MAX_RES_W                   ( MAX_RES_W                         ),
        .RES_CNT                     ( RES_CNT                           ),
        .RES_W                       ( RES_W                             ),
        .RES_MASK                    ( RES_MASK           [RES_CNT-1:0]  ),
        .RES_XREG                    ( '0                                ),
        .RES_NARROW                  ( RES_NARROW         [RES_CNT-1:0]  ),
        .RES_ALLOW_ELEMWISE          ( RES_ALLOW_ELEMWISE [RES_CNT-1:0]  ),
        .RES_ALWAYS_ELEMWISE         ( RES_ALWAYS_ELEMWISE[RES_CNT-1:0]  ),
        .FLAGS_T                     ( pack_flags                        ),
        .INSTR_ID_W                  ( XIF_ID_W                          ),
        .INSTR_ID_CNT                ( XIF_ID_CNT                        ),
        .DONT_CARE_ZERO              ( DONT_CARE_ZERO                    )
    ) pack (
        .clk_i                       ( clk_i                             ),
        .async_rst_ni                ( async_rst_ni                      ),
        .sync_rst_ni                 ( sync_rst_ni                       ),
        .pipe_in_valid_i             ( unit_out_valid                    ),
        .pipe_in_ready_o             ( unit_out_ready                    ),
        .pipe_in_instr_id_i          ( unit_out_ctrl.id                  ),
        .pipe_in_eew_i               ( unit_out_ctrl.eew                 ),
        .pipe_in_vaddr_i             ( unit_out_ctrl.res_vaddr           ),
        .pipe_in_res_store_i         ( pack_res_store                    ),
        .pipe_in_res_valid_i         ( pack_res_valid                    ),
        .pipe_in_res_flags_i         ( pack_res_flags                    ),
        .pipe_in_res_data_i          ( pack_res_data                     ),
        .pipe_in_res_mask_i          ( pack_res_mask                     ),
        .pipe_in_pend_clr_i          ( pack_pend_clear                   ),
        .pipe_in_pend_clr_cnt_i      ( pack_pend_clear_cnt               ),
        .pipe_in_instr_done_i        ( unit_out_instr_done               ),
        .vreg_wr_valid_o             ( vreg_wr_en_o                      ),
        .vreg_wr_ready_i             ( 1'b1                              ),
        .vreg_wr_addr_o              ( vreg_wr_addr_o                    ),
        .vreg_wr_be_o                ( vreg_wr_mask_o                    ),
        .vreg_wr_data_o              ( vreg_wr_o                         ),
        .pending_vreg_reads_i        ( pack_pending_vreg_reads           ),
        .clear_pending_vreg_writes_o ( clear_wr_hazards_o                ),
        .instr_spec_i                ( pack_instr_spec                   ),
        .instr_killed_i              ( pack_instr_killed                 ),
        .instr_done_valid_o          ( pack_instr_done_valid             ),
        .instr_done_id_o             ( pack_instr_done_id                )
    );


`ifdef VPROC_SVA
`include "vproc_pipeline_sva.svh"
`endif

endmodule
