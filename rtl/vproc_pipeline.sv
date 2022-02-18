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


    ///////////////////////////////////////////////////////////////////////////
    // STATE LOGIC

    localparam int unsigned CYCLES_PER_VREG = VREG_W / ((UNIT == UNIT_ELEM) ? 8 : MAX_OP_W);
    localparam int unsigned COUNTER_W       = $clog2(CYCLES_PER_VREG) + 4;

    localparam int unsigned STRIDE_ELEMS_PER_VMEM = MAX_OP_W / 8; // maximum number of elems read at once for strided/indexed loads
    localparam int unsigned STRIDE_COUNTER_W      = $clog2(STRIDE_ELEMS_PER_VMEM);

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

    typedef struct packed {
        counter_t                    count;
        logic [STRIDE_COUNTER_W-1:0] count_stride;
        logic [GATHER_COUNTER_W-1:0] count_gather;
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
        logic                        vl_mask;
        op_regs                      rs1;
        logic                        vs1_narrow;
        logic                        vs1_fetch;
        logic                        vs1_shift;
        op_regs                      rs2;
        logic                        vs2_narrow;
        logic                        vs2_fetch;
        logic                        vs2_shift;
        logic                        v0msk_fetch;
        logic                        v0msk_shift;
        logic                        vs3_fetch;
        logic                        vs3_shift;
        logic                        gather_fetch;
        logic [4:0]                  vd;
        logic                        vd_narrow;
        logic                        vd_store;
    } ctrl_t;

    logic        state_valid_q,  state_valid_d;
    ctrl_t       state_q,        state_d;
    logic [31:0] vreg_pend_wr_q, vreg_pend_wr_d; // local copy of global vreg write mask
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
    end

    logic last_cycle;
    always_comb begin
        last_cycle = DONT_CARE_ZERO ? 1'b0 : 1'bx;
        unique case (state_q.emul)
            EMUL_1: last_cycle =                                        state_q.count.part.low == '1;
            EMUL_2: last_cycle = (state_q.count.part.mul[  0] == '1) & (state_q.count.part.low == '1);
            EMUL_4: last_cycle = (state_q.count.part.mul[1:0] == '1) & (state_q.count.part.low == '1);
            EMUL_8: last_cycle = (state_q.count.part.mul[2:0] == '1) & (state_q.count.part.low == '1);
            default: ;
        endcase
        if ((UNIT == UNIT_LSU) & state_q.count_stride != '1) begin
            last_cycle = '0;
        end
        if ((UNIT == UNIT_SLD) & state_q.count.part.sign) begin
            last_cycle = '0;
        end
        if ((UNIT == UNIT_ELEM) & (state_q.count_gather != '1)) begin
            last_cycle = '0;
        end
    end

    counter_t slide_count;
    always_comb begin
        slide_count.val = state_q.rs1.r.xval[$clog2(MAX_OP_W/8) +: COUNTER_W];
        if (state_q.mode.sld.slide1) begin
            if (state_q.mode.sld.dir == SLD_UP) begin
                // slide_count is all zeroes for up slide, except for a byte slide of 4 when the
                // operand width is 32 bits, then it is 1 (right shift by log2(MAX_OP_W/8) = 2 bits)
                unique case (state_q.eew)
                    VSEW_8,
                    VSEW_16: slide_count.val = '0;
                    VSEW_32: slide_count.val = {{COUNTER_W-1{1'b0}}, MAX_OP_W == 32};
                    default: ;
                endcase
            end else begin
                // slide_count is all ones for down slide, even with a byte slide value of -4
                slide_count.val = '1;
            end
        end
    end

    logic [3:0] slide_mul_diff;
    assign slide_mul_diff = state_q.count.val[COUNTER_W-1 -: 4] - slide_count.val[COUNTER_W-1 -: 4];

    logic slide_fetch;
    always_comb begin
        slide_fetch = 1'b0;
        if (state_q.count.part.low == slide_count.part.low) begin
            unique case (state_q.emul)
                EMUL_1: slide_fetch =   slide_mul_diff             == '0;
                EMUL_2: slide_fetch = ((slide_mul_diff) & 4'b1110) == '0;
                EMUL_4: slide_fetch = ((slide_mul_diff) & 4'b1100) == '0;
                EMUL_8: slide_fetch = ((slide_mul_diff) & 4'b1000) == '0;
                default: ;
            endcase
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
    always_comb begin
        op_ack_o       = 1'b0;
        state_valid_d  = state_valid_q;
        state_d        = state_q;
        vreg_pend_wr_d = vreg_pend_wr_q & vreg_pend_wr_i;

        if (((~state_valid_q) | (last_cycle & pipeline_ready & ((UNIT != UNIT_ELEM) | ~state_q.requires_flush))) & op_rdy_i) begin
            op_ack_o            = 1'b1;
            state_valid_d       = 1'b1;
            state_d.count.val   = '0;
            if ((UNIT == UNIT_SLD) & (mode_i.sld.dir == SLD_DOWN)) begin
                state_d.count.part.sign = '1;
                state_d.count.part.mul  = '1;
            end
            if (UNIT == UNIT_ELEM) begin
                state_d.count.val[1:0] = DONT_CARE_ZERO ? '0 : 'x;
                unique case (vsew_i)
                    VSEW_8:  state_d.count.val[1:0] = 2'b00;
                    VSEW_16: state_d.count.val[1:0] = 2'b01;
                    VSEW_32: state_d.count.val[1:0] = 2'b11;
                    default: ;
                endcase
            end
            // LSU stride counter
            if (mode_i.lsu.stride == LSU_UNITSTRIDE) begin
                state_d.count_stride = '1;
            end else begin
                state_d.count_stride = DONT_CARE_ZERO ? '0 : 'x;
                unique case (mode_i.lsu.eew)
                    VSEW_8:  state_d.count_stride = '0;
                    VSEW_16: state_d.count_stride = STRIDE_COUNTER_W'(1);
                    VSEW_32: state_d.count_stride = STRIDE_COUNTER_W'(3);
                    default: ;
                endcase
            end
            // ELEM gather counter
            state_d.count_gather   = (mode_i.elem.op == ELEM_VRGATHER) ? '0 : '1;
            state_d.first_cycle    = 1'b1;
            state_d.requires_flush = (UNIT == UNIT_ELEM) & ((mode_i.elem.op == ELEM_VCOMPRESS) | op_reduction);
            state_d.id             = id_i;
            state_d.mode           = mode_i;
            state_d.emul           = emul_i;
            state_d.eew            = (UNIT == UNIT_LSU) ? mode_i.lsu.eew : vsew_i;
            state_d.vxrm           = vxrm_i;
            state_d.vl             = vl_i;
            state_d.vl_0           = vl_0_i;
            state_d.vl_mask        = ~vl_0_i;
            state_d.rs1            = rs1_i;
            state_d.rs1            = ((UNIT == UNIT_ELEM) & ((mode_i.elem.op == ELEM_XMV) | op_reduction)) ? rs2_i : rs1_i;
            state_d.rs1.vreg       = ((UNIT == UNIT_ELEM) & ((mode_i.elem.op == ELEM_XMV) | op_reduction)) | rs1_i.vreg;
            if ((UNIT == UNIT_SLD) & ~mode_i.sld.slide1) begin
                // convert element offset to byte offset for the relevant section of rs1 and negate
                // for down slides
                if (mode_i.sld.dir == SLD_UP) begin
                    unique case (vsew_i)
                        VSEW_8:  state_d.rs1.r.xval[$clog2(VREG_W/8)+3:0] =  {1'b0, rs1_i.r.xval[$clog2(VREG_W/8)+2:0]      };
                        VSEW_16: state_d.rs1.r.xval[$clog2(VREG_W/8)+3:0] =  {1'b0, rs1_i.r.xval[$clog2(VREG_W/8)+1:0], 1'b0};
                        VSEW_32: state_d.rs1.r.xval[$clog2(VREG_W/8)+3:0] =  {1'b0, rs1_i.r.xval[$clog2(VREG_W/8)+0:0], 2'b0};
                        default: ;
                    endcase
                end else begin
                    unique case (vsew_i)
                        VSEW_8:  state_d.rs1.r.xval[$clog2(VREG_W/8)+3:0] = -{1'b0, rs1_i.r.xval[$clog2(VREG_W/8)+2:0]      };
                        VSEW_16: state_d.rs1.r.xval[$clog2(VREG_W/8)+3:0] = -{1'b0, rs1_i.r.xval[$clog2(VREG_W/8)+1:0], 1'b0};
                        VSEW_32: state_d.rs1.r.xval[$clog2(VREG_W/8)+3:0] = -{1'b0, rs1_i.r.xval[$clog2(VREG_W/8)+0:0], 2'b0};
                        default: ;
                    endcase
                end
            end
            state_d.vs1_narrow  = widenarrow_i != OP_SINGLEWIDTH;
            state_d.vs1_fetch   = ((UNIT == UNIT_ELEM) & ((mode_i.elem.op == ELEM_XMV) | op_reduction)) | rs1_i.vreg;
            //state_d.vs1_shift   = 1'b1;
            state_d.rs2         = ((UNIT == UNIT_ELEM) & op_reduction) ? rs1_i : rs2_i;
            state_d.rs2.vreg    = ((UNIT == UNIT_ELEM) & op_reduction) | rs2_i.vreg;
            if (UNIT == UNIT_SLD) begin
                state_d.rs2.vreg = 1'b0; // use vreg bit as valid signal
            end
            state_d.vs2_narrow   = widenarrow_i == OP_WIDENING;
            state_d.vs2_fetch    = ((UNIT == UNIT_LSU) | (UNIT == UNIT_ALU)) ? rs2_i.vreg : 1'b1;
            //state_d.vs2_shift   = 1'b1;
            state_d.v0msk_fetch  = (UNIT == UNIT_SLD) ? (mode_i.sld.dir == SLD_UP) : 1'b1;
            //state_d.v0msk_shift = 1'b1;
            state_d.vs3_fetch    = (UNIT == UNIT_LSU) ? mode_i.lsu.store : (
                                   (UNIT == UNIT_MUL) ? (mode_i.mul.op == MUL_VMACC) : '0);
            state_d.gather_fetch = 1'b1;
            state_d.vd           = vd_i;
            state_d.vd_narrow    = (UNIT == UNIT_ALU) ? (widenarrow_i == OP_NARROWING) : '0;
            state_d.vd_store     = 1'b0;
            vreg_pend_wr_d       = vreg_pend_wr_i;
        end
        else if (state_valid_q & pipeline_ready) begin
            if (UNIT == UNIT_LSU) begin
                state_valid_d = ~last_cycle;
                if ((state_q.mode.lsu.stride == LSU_UNITSTRIDE) | (state_q.count_stride == '1)) begin
                    state_d.count.val = state_q.count.val + 1;
                end
                if (state_q.mode.lsu.stride != LSU_UNITSTRIDE) begin
                    unique case (state_q.mode.lsu.eew)
                        VSEW_8:  state_d.count_stride = state_q.count_stride + STRIDE_COUNTER_W'(1);
                        VSEW_16: state_d.count_stride = state_q.count_stride + STRIDE_COUNTER_W'(2);
                        VSEW_32: state_d.count_stride = state_q.count_stride + STRIDE_COUNTER_W'(4);
                        default: ;
                    endcase
                end
                unique case (state_q.mode.lsu.stride)
                    LSU_UNITSTRIDE: state_d.rs1.r.xval = state_q.rs1.r.xval + (MAX_OP_W / 8);
                    LSU_STRIDED:    state_d.rs1.r.xval = state_q.rs1.r.xval + state_q.rs2.r.xval;
                    default: ; // for indexed loads the base address stays the same
                endcase
            end
            else if (UNIT == UNIT_ELEM) begin
                state_valid_d = ~last_cycle | state_q.requires_flush;
                if (state_q.count_gather == '1) begin
                    unique case (state_q.eew)
                        VSEW_8:  state_d.count.val = state_q.count.val + 1;
                        VSEW_16: state_d.count.val = state_q.count.val + 2;
                        VSEW_32: state_d.count.val = state_q.count.val + 4;
                        default: ;
                    endcase
                end
                if (state_q.mode.elem.op == ELEM_VRGATHER) begin
                    state_d.count_gather = state_q.count_gather + 1;
                end
                if (last_cycle & state_q.requires_flush) begin
                    state_d.count.val      = '0;
                    state_d.count.val[1:0] = DONT_CARE_ZERO ? '0 : 'x;
                    unique case (vsew_i)
                        VSEW_8:  state_d.count.val[1:0] = 2'b00;
                        VSEW_16: state_d.count.val[1:0] = 2'b01;
                        VSEW_32: state_d.count.val[1:0] = 2'b11;
                        default: ;
                    endcase
                    state_d.count.part.mul = '1; // flush only one vreg
                    state_d.mode.elem.op   = ELEM_FLUSH;
                    state_d.requires_flush = 1'b0;
                    state_d.rs1.vreg       = 1'b0;
                end
            end else begin
                state_valid_d     = ~last_cycle;
                state_d.count.val = state_q.count.val + 1;
            end
            state_d.first_cycle  = 1'b0;
            state_d.vs1_fetch    = 1'b0;
            state_d.vs2_fetch    = 1'b0;
            state_d.vs3_fetch    = 1'b0;
            state_d.gather_fetch = 1'b0;
            state_d.vd_store     = 1'b0;
            if ((state_q.count.part.low == '1) & ((UNIT != UNIT_ELEM) | state_q.count_gather == '1)) begin
                if ((UNIT != UNIT_LSU) & state_q.rs1.vreg & (~state_q.vs1_narrow | state_q.count.part.mul[0])) begin
                    state_d.rs1.r.vaddr[2:0] = state_q.rs1.r.vaddr[2:0] + 3'b1;
                    state_d.vs1_fetch        = state_q.rs1.vreg & ((UNIT != UNIT_ELEM) | ~last_cycle);
                end
                if ((UNIT != UNIT_SLD) & (UNIT != UNIT_ELEM) & (~state_q.vs2_narrow | state_q.count.part.mul[0])) begin
                    if ((UNIT != UNIT_LSU) | ((state_q.count_stride == '1) & state_q.rs2.vreg)) begin
                        state_d.rs2.r.vaddr[2:0] = state_q.rs2.r.vaddr[2:0] + 3'b1;
                        state_d.vs2_fetch        = state_q.rs2.vreg;
                    end
                end
                unique case (UNIT)
                    UNIT_LSU: if (state_q.count_stride == '1) begin
                        state_d.vd[2:0] = state_q.vd[2:0] + 3'b1;
                    end
                    UNIT_ALU: if (~state_q.mode.alu.cmp & (~state_q.vd_narrow | state_q.count.part.mul[0])) begin
                        state_d.vd[2:0] = state_q.vd[2:0] + 3'b1;
                    end
                    UNIT_SLD: if (~state_q.count.part.sign) begin
                        state_d.vd[2:0] = state_q.vd[2:0] + 3'b1;
                    end
                    UNIT_MUL: begin
                        state_d.vd[2:0] = state_q.vd[2:0] + 3'b1;
                    end
                    default: ;
                endcase
                state_d.vs3_fetch = (UNIT == UNIT_MUL) ? (state_q.mode.mul.op == MUL_VMACC) : '0;
                if ((UNIT == UNIT_LSU) & (state_q.count_stride == '1)) begin
                    state_d.vs3_fetch = state_q.mode.lsu.store;
                end
            end
            if (UNIT == UNIT_LSU) begin
                unique case (state_q.mode.lsu.eew)
                    VSEW_8:  state_d.vs2_shift = state_q.count_stride[1:0] == '1;
                    VSEW_16: state_d.vs2_shift = state_q.count_stride[1  ];
                    VSEW_32: state_d.vs2_shift = 1'b1;
                    default: ;
                endcase
            end
            else if (UNIT == UNIT_ELEM) begin
                if (~state_q.vs1_narrow) begin
                    state_d.vs1_shift = state_q.count.val[1:0] == '1;
                end else begin
                    state_d.vs1_shift = state_q.count.val[2:0] == '1;
                end
                state_d.vs2_shift = DONT_CARE_ZERO ? '0 : 'x;
                case (state_q.eew)
                    VSEW_8:  state_d.vs2_shift = 5'(state_q.count) == '1;
                    VSEW_16: state_d.vs2_shift = 6'(state_q.count) == '1;
                    VSEW_32: state_d.vs2_shift = 7'(state_q.count) == '1;
                    default: ;
                endcase
            end else begin
                state_d.vs1_shift = ~state_q.vs1_narrow | state_q.count.part.low[0];
                state_d.vs2_shift = ~state_q.vs2_narrow | state_q.count.part.low[0];
            end
            state_d.gather_fetch = (UNIT == UNIT_ELEM) & (state_q.count_gather == '1);
            state_d.v0msk_fetch  = (UNIT == UNIT_SLD) ? state_q.count.part.sign : '0;
            state_d.v0msk_shift  = '0;
            unique case (state_q.eew)
                VSEW_8:  state_d.v0msk_shift = 1'b1;
                VSEW_16: state_d.v0msk_shift = state_q.count.val[0];
                VSEW_32: state_d.v0msk_shift = state_q.count.val[1:0] == '1;
                default: ;
            endcase
            if ((UNIT == UNIT_LSU) & (state_q.count_stride != '1)) begin
                state_d.v0msk_shift = 1'b0;
            end
            if ((UNIT == UNIT_SLD) & (state_q.count.part.low == slide_count.part.low)) begin
                state_d.rs2.vreg = slide_fetch; // set vs2 valid bit after fetch
            end
            state_d.vs3_shift = (UNIT == UNIT_LSU) & (state_q.count_stride == '1);
        end
    end


    ///////////////////////////////////////////////////////////////////////////
    // FIRST STAGE

    logic  state_init_stall;
    logic  state_init_valid;
    ctrl_t state_init;
    logic  state_init_masked;
    always_comb begin
        state_init_valid      = state_valid_q;
        state_init            = state_q;
        state_init.last_cycle = state_valid_q & last_cycle;
        state_init.vl_mask    = ~state_q.vl_0 & (CFG_VL_W'(state_q.count.val) <= state_q.vl);
        state_init.vd_store   = '0;
        if (state_q.count.part.low == '1) begin
            unique case (UNIT)
                UNIT_LSU: state_init.vd_store = state_q.count_stride == '1;
                UNIT_ALU: state_init.vd_store = ~state_q.vd_narrow | state_q.count.part.mul[0];
                UNIT_SLD: state_init.vd_store = ~state_q.count.part.sign;
                UNIT_MUL: state_init.vd_store = 1'b1;
                default: ;
            endcase
        end
        if (UNIT == UNIT_SLD) begin
            unique case (state_q.emul)
                EMUL_2: state_init.rs2.r.vaddr[0:0] = slide_mul_diff[0:0];
                EMUL_4: state_init.rs2.r.vaddr[1:0] = slide_mul_diff[1:0];
                EMUL_8: state_init.rs2.r.vaddr[2:0] = slide_mul_diff[2:0];
                default: ;
            endcase
            state_init.rs2.vreg  = slide_fetch | state_q.rs2.vreg;
            state_init.vs2_fetch = slide_fetch;
        end

        // Determine whether there is a pending read of v0 as a mask
        state_init_masked = '0;
        unique case (UNIT)
            UNIT_LSU:  state_init_masked = state_init.mode.lsu.masked;
            UNIT_ALU:  state_init_masked = state_init.mode.alu.op_mask != ALU_MASK_NONE;
            UNIT_MUL:  state_init_masked = state_init.mode.mul.masked;
            UNIT_SLD:  state_init_masked = state_init.mode.sld.masked;
            UNIT_ELEM: state_init_masked = state_init.mode.elem.masked;
            default: ;
        endcase
    end
    logic unpack_ready;
    assign pipeline_ready = unpack_ready & ~state_init_stall;


    logic [31:0] state_init_gather_vregs;
    always_comb begin
        state_init_gather_vregs = DONT_CARE_ZERO ? '0 : 'x;
        unique case (state_init.emul)
            EMUL_1: state_init_gather_vregs = 32'h01 <<  state_init.rs2.r.vaddr;
            EMUL_2: state_init_gather_vregs = 32'h03 << {state_init.rs2.r.vaddr[4:1], 1'b0};
            EMUL_4: state_init_gather_vregs = 32'h0F << {state_init.rs2.r.vaddr[4:2], 2'b0};
            EMUL_8: state_init_gather_vregs = 32'hFF << {state_init.rs2.r.vaddr[4:3], 3'b0};
            default: ;
        endcase
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
    generate
        if (UNIT == UNIT_LSU) begin
            assign state_init_stall = (state_init.vs2_fetch   & vreg_pend_wr_q[state_init.rs2.r.vaddr]) |
                                      (state_init.vs3_fetch   & vreg_pend_wr_q[state_init.vd         ]) |
                                      (state_init.v0msk_fetch & state_init_masked & vreg_pend_wr_q[0]);
        end
        else if (UNIT == UNIT_ALU) begin
            assign state_init_stall = (state_init.vs1_fetch   & vreg_pend_wr_q[state_init.rs1.r.vaddr]) |
                                      (state_init.vs2_fetch   & vreg_pend_wr_q[state_init.rs2.r.vaddr]) |
                                      (state_init.v0msk_fetch & state_init_masked & vreg_pend_wr_q[0]);
        end
        else if (UNIT == UNIT_MUL) begin
            assign state_init_stall = (state_init.vs1_fetch   & vreg_pend_wr_q[state_init.rs1.r.vaddr]) |
                                      (state_init.vs2_fetch   & vreg_pend_wr_q[state_init.rs2.r.vaddr]) |
                                      (state_init.vs3_fetch   & vreg_pend_wr_q[state_init.vd         ]) |
                                      (state_init.v0msk_fetch & state_init_masked & vreg_pend_wr_q[0]);
        end
        else if (UNIT == UNIT_SLD) begin
            assign state_init_stall = (state_init.vs2_fetch   & vreg_pend_wr_q[state_init.rs2.r.vaddr]) |
                                      (state_init.v0msk_fetch & state_init_masked & vreg_pend_wr_q[0]);
        end
        else if (UNIT == UNIT_ELEM) begin
            assign state_init_stall = (state_init.vs1_fetch                                                                      & vreg_pend_wr_q[state_init.rs1.r.vaddr]) |
                                      (state_init.rs2.vreg & state_init.first_cycle & (state_init.mode.elem.op != ELEM_VRGATHER) & vreg_pend_wr_q[state_init.rs2.r.vaddr]) |
                                      ((state_init.mode.elem.op == ELEM_VRGATHER) & ((state_init_gather_vregs & vreg_pend_wr_q) != '0)) |
                                      (state_init.v0msk_fetch & state_init_masked & vreg_pend_wr_q[0]);
        end
    endgenerate

    // pending vreg reads
    // Note: The pipeline might stall while reading a vreg, hence a vreg has to
    // be part of the pending reads until the read is complete.
    logic [31:0] pend_vs1, pend_vs2, pend_vs3;
    always_comb begin
        pend_vs1 = DONT_CARE_ZERO ? '0 : 'x;
        unique case (UNIT)
            UNIT_ALU, UNIT_MUL: begin
                unique case ({state_init.emul, state_init.vs1_narrow})
                    {EMUL_1, 1'b0}: pend_vs1 = {31'b0, state_init.vs1_fetch} << state_init.rs1.r.vaddr;
                    {EMUL_2, 1'b1}: pend_vs1 = {31'b0, state_init.vs1_fetch} << state_init.rs1.r.vaddr;
                    {EMUL_2, 1'b0}: pend_vs1 = (32'h03 & ((32'h02 | {31'b0, state_init.vs1_fetch}) << state_init.count.part.mul[2:0])) << {state_init.rs1.r.vaddr[4:1], 1'b0};
                    {EMUL_4, 1'b1}: pend_vs1 = (32'h03 & ((32'h02 | {31'b0, state_init.vs1_fetch}) << state_init.count.part.mul[2:1])) << {state_init.rs1.r.vaddr[4:1], 1'b0};
                    {EMUL_4, 1'b0}: pend_vs1 = (32'h0F & ((32'h0E | {31'b0, state_init.vs1_fetch}) << state_init.count.part.mul[2:0])) << {state_init.rs1.r.vaddr[4:2], 2'b0};
                    {EMUL_8, 1'b1}: pend_vs1 = (32'h0F & ((32'h0E | {31'b0, state_init.vs1_fetch}) << state_init.count.part.mul[2:1])) << {state_init.rs1.r.vaddr[4:2], 2'b0};
                    {EMUL_8, 1'b0}: pend_vs1 = (32'hFF & ((32'hFE | {31'b0, state_init.vs1_fetch}) << state_init.count.part.mul[2:0])) << {state_init.rs1.r.vaddr[4:3], 3'b0};
                    default: ;
                endcase
            end
            UNIT_ELEM: begin
                unique case ({state_init.emul, state_init.vs1_narrow})
                    {EMUL_1, 1'b0}: pend_vs1 = 32'h01 <<  state_init.rs1.r.vaddr;
                    {EMUL_2, 1'b1}: pend_vs1 = 32'h01 <<  state_init.rs1.r.vaddr;
                    {EMUL_2, 1'b0}: pend_vs1 = 32'h03 << {state_init.rs1.r.vaddr[4:1], 1'b0};
                    {EMUL_4, 1'b1}: pend_vs1 = 32'h03 << {state_init.rs1.r.vaddr[4:1], 1'b0};
                    {EMUL_4, 1'b0}: pend_vs1 = 32'h0F << {state_init.rs1.r.vaddr[4:2], 2'b0};
                    {EMUL_8, 1'b1}: pend_vs1 = 32'h0F << {state_init.rs1.r.vaddr[4:2], 2'b0};
                    {EMUL_8, 1'b0}: pend_vs1 = 32'hFF << {state_init.rs1.r.vaddr[4:3], 3'b0};
                    default: ;
                endcase
            end
            default: ;
        endcase
        pend_vs2 = DONT_CARE_ZERO ? '0 : 'x;
        unique case (UNIT)
            UNIT_LSU: begin
                unique case (state_init.emul)
                    EMUL_1: pend_vs2 = {31'b0, state_init.vs2_fetch} << state_init.rs2.r.vaddr;
                    EMUL_2: pend_vs2 = (32'h03 & ((32'h02 | {31'b0, state_init.vs2_fetch}) << state_init.count.part.mul[2:0])) << {state_init.rs2.r.vaddr[4:1], 1'b0};
                    EMUL_4: pend_vs2 = (32'h0F & ((32'h0E | {31'b0, state_init.vs2_fetch}) << state_init.count.part.mul[2:0])) << {state_init.rs2.r.vaddr[4:2], 2'b0};
                    EMUL_8: pend_vs2 = (32'hFF & ((32'hFE | {31'b0, state_init.vs2_fetch}) << state_init.count.part.mul[2:0])) << {state_init.rs2.r.vaddr[4:3], 3'b0};
                    default: ;
                endcase
            end
            UNIT_ALU, UNIT_MUL: begin
                unique case ({state_init.emul, state_init.vs2_narrow})
                    {EMUL_1, 1'b0}: pend_vs2 = {31'b0, state_init.vs2_fetch} << state_init.rs2.r.vaddr;
                    {EMUL_2, 1'b1}: pend_vs2 = {31'b0, state_init.vs2_fetch} << state_init.rs2.r.vaddr;
                    {EMUL_2, 1'b0}: pend_vs2 = (32'h03 & ((32'h02 | {31'b0, state_init.vs2_fetch}) << state_init.count.part.mul[2:0])) << {state_init.rs2.r.vaddr[4:1], 1'b0};
                    {EMUL_4, 1'b1}: pend_vs2 = (32'h03 & ((32'h02 | {31'b0, state_init.vs2_fetch}) << state_init.count.part.mul[2:1])) << {state_init.rs2.r.vaddr[4:1], 1'b0};
                    {EMUL_4, 1'b0}: pend_vs2 = (32'h0F & ((32'h0E | {31'b0, state_init.vs2_fetch}) << state_init.count.part.mul[2:0])) << {state_init.rs2.r.vaddr[4:2], 2'b0};
                    {EMUL_8, 1'b1}: pend_vs2 = (32'h0F & ((32'h0E | {31'b0, state_init.vs2_fetch}) << state_init.count.part.mul[2:1])) << {state_init.rs2.r.vaddr[4:2], 2'b0};
                    {EMUL_8, 1'b0}: pend_vs2 = (32'hFF & ((32'hFE | {31'b0, state_init.vs2_fetch}) << state_init.count.part.mul[2:0])) << {state_init.rs2.r.vaddr[4:3], 3'b0};
                    default: ;
                endcase
            end
            UNIT_SLD: begin
                unique case (state_q.emul)
                    EMUL_1: pend_vs2 = 32'h01 <<  state_q.rs2.r.vaddr;
                    EMUL_2: pend_vs2 = 32'h03 << {state_q.rs2.r.vaddr[4:1], 1'b0};
                    EMUL_4: pend_vs2 = 32'h0F << {state_q.rs2.r.vaddr[4:2], 2'b0};
                    EMUL_8: pend_vs2 = 32'hFF << {state_q.rs2.r.vaddr[4:3], 3'b0};
                    default: ;
                endcase
            end
            UNIT_ELEM: begin
                // vs2 is either:
                //  - a mask vreg, which is always a single vreg read in the first cycle
                //  - the init vreg for reductions, which is also a single vreg read in the first cycle
                //    (for reductions vs1 and vs2 are swapped, so actually this is vs1)
                //  - the gather register group
                pend_vs2 = DONT_CARE_ZERO ? '0 : 'x;
                if (state_init.mode.elem.op == ELEM_VRGATHER) begin
                    // entire gather register group remains pending throughout the operation
                    pend_vs2 = state_init_gather_vregs;
                end else begin
                    // mask/init register is read right at the beginning
                    pend_vs2 = state_init.first_cycle ? (32'h01 << state_init.rs2.r.vaddr) : '0;
                end
            end
            default: ;
        endcase
        pend_vs3 = DONT_CARE_ZERO ? '0 : 'x;
        unique case (state_init.emul)
            EMUL_1: pend_vs3 = {31'b0, state_init.vs3_fetch} << state_init.vd;
            EMUL_2: pend_vs3 = (32'h03 & ((32'h02 | {31'b0, state_init.vs3_fetch}) << state_init.count.part.mul[2:0])) << {state_init.vd[4:1], 1'b0};
            EMUL_4: pend_vs3 = (32'h0F & ((32'h0E | {31'b0, state_init.vs3_fetch}) << state_init.count.part.mul[2:0])) << {state_init.vd[4:2], 2'b0};
            EMUL_8: pend_vs3 = (32'hFF & ((32'hFE | {31'b0, state_init.vs3_fetch}) << state_init.count.part.mul[2:0])) << {state_init.vd[4:3], 3'b0};
            default: ;
        endcase
    end
    // Note: vs2 is read in the second cycle; the v0 mask has no extra buffer
    // and is always read in state_vs1
    logic [31:0] unpack_pend_rd;
    generate
        if (UNIT == UNIT_LSU) begin
            assign vreg_pend_rd_o = ((
                    ((state_init_valid & state_init.rs2.vreg      ) ? pend_vs2                   : '0) |
                    ((state_init_valid & state_init.mode.lsu.store) ? pend_vs3                   : '0) |
                    ((state_init_valid & state_init.v0msk_fetch   ) ? {31'b0, state_init_masked} : '0)
                ) & ~vreg_pend_wr_q) |
            unpack_pend_rd;
        end
        else if (UNIT == UNIT_ALU) begin
            assign vreg_pend_rd_o = ((
                    ((state_init_valid & state_init.rs1.vreg   ) ? pend_vs1                   : '0) |
                    ((state_init_valid & state_init.rs2.vreg   ) ? pend_vs2                   : '0) |
                    ((state_init_valid & state_init.v0msk_fetch) ? {31'b0, state_init_masked} : '0)
                ) & ~vreg_pend_wr_q) |
            unpack_pend_rd;
        end
        else if (UNIT == UNIT_MUL) begin
            assign vreg_pend_rd_o = ((
                    ((state_init_valid & state_init.rs1.vreg                  ) ? pend_vs1                   : '0) |
                    ((state_init_valid                                        ) ? pend_vs2                   : '0) |
                    ((state_init_valid & (state_init.mode.mul.op == MUL_VMACC)) ? pend_vs3                   : '0) |
                    ((state_init_valid & state_init.v0msk_fetch               ) ? {31'b0, state_init_masked} : '0)
                ) & ~vreg_pend_wr_q) |
            unpack_pend_rd;
        end
        else if (UNIT == UNIT_SLD) begin
            assign vreg_pend_rd_o = ((
                    ( state_init_valid                                                          ? pend_vs2                   : '0) |
                    ((state_init_valid & (state_init.count.part.sign | state_init.v0msk_fetch)) ? {31'b0, state_init_masked} : '0)
                ) & ~vreg_pend_wr_q) |
            unpack_pend_rd;
        end
        else if (UNIT == UNIT_ELEM) begin
            assign vreg_pend_rd_o = ((
                    ((state_init_valid & state_init.rs1.vreg   ) ? pend_vs1                   : '0) |
                    ((state_init_valid & state_init.rs2.vreg   ) ? pend_vs2                   : '0) |
                    ((state_init_valid & state_init.v0msk_fetch) ? {31'b0, state_init_masked} : '0)
                ) & ~vreg_pend_wr_q) |
            pending_gather_vreg_reads_q | unpack_pend_rd;
        end
    endgenerate

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

    logic        [OP_CNT-1:0]       unpack_op_load;
    logic        [OP_CNT-1:0][4 :0] unpack_op_vaddr;
    unpack_flags [OP_CNT-1:0]       unpack_op_flags;
    logic        [OP_CNT-1:0][31:0] unpack_op_xval;
    generate
        if (OP_CNT == 2) begin
            always_comb begin
                unpack_op_flags[0]          = unpack_flags'('0);
                unpack_op_flags[0].shift    = 1'b1;
                unpack_op_load [0]          = state_init.vs2_fetch;
                unpack_op_flags[0].elemwise = '0;
                unpack_op_vaddr[0]          = state_init.rs2.r.vaddr;
                unpack_op_xval [0]          = '0;
            end
        end else begin
            always_comb begin
                unpack_op_load [0]          = state_init.vs1_fetch;
                unpack_op_vaddr[0]          = state_init.rs1.r.vaddr;
                unpack_op_flags[0]          = unpack_flags'('0);
                unpack_op_flags[0].shift    = state_init.vs1_shift;
                unpack_op_xval [0]          = state_init.rs1.r.xval;
                unpack_op_load [1]          = state_init.vs2_fetch;
                unpack_op_vaddr[1]          = state_init.rs2.r.vaddr;
                unpack_op_flags[1]          = unpack_flags'('0);
                unpack_op_flags[1].shift    = state_init.vs2_shift;
                unpack_op_xval [1]          = '0;
                if (UNIT == UNIT_LSU) begin
                    unpack_op_load [0]          = state_init.vs2_fetch;
                    unpack_op_vaddr[0]          = state_init.rs2.r.vaddr;
                    unpack_op_flags[0].shift    = state_init.vs2_shift;
                    unpack_op_load [1]          = state_init.vs3_fetch;
                    unpack_op_vaddr[1]          = state_init.vd;
                    unpack_op_flags[1].shift    = state_init.vs3_shift;
                end
                else if (UNIT == UNIT_ALU) begin
                    unpack_op_flags[0].vreg     = state_init.rs1.vreg;
                    unpack_op_flags[0].narrow   = state_init.vs1_narrow;
                    unpack_op_flags[0].sigext   = state_init.mode.alu.sigext;
                    unpack_op_flags[1].narrow   = state_init.vs2_narrow;
                    unpack_op_flags[1].sigext   = state_init.mode.alu.sigext;
                end
                else if (UNIT == UNIT_MUL) begin
                    unpack_op_flags[0].vreg     = state_init.rs1.vreg;
                    unpack_op_flags[0].narrow   = state_init.vs1_narrow;
                    unpack_op_flags[0].sigext   = state_init.mode.mul.op1_signed;
                    unpack_op_flags[1].narrow   = state_init.vs2_narrow;
                    unpack_op_flags[1].sigext   = state_init.mode.mul.op2_signed;
                    unpack_op_vaddr[1]          = state_init.mode.mul.op2_is_vd ? state_init.vd : state_init.rs2.r.vaddr;
                    unpack_op_load [2]          = state_init.vs3_fetch;
                    unpack_op_vaddr[2]          = state_init.mode.mul.op2_is_vd ? state_init.rs2.r.vaddr : state_init.vd;
                    unpack_op_flags[2]          = unpack_flags'('0);
                    unpack_op_flags[2].shift    = 1'b1;
                    unpack_op_flags[2].elemwise = '0;
                    unpack_op_flags[2].narrow   = '0;
                    unpack_op_flags[2].sigext   = '0;
                    unpack_op_xval [2]          = '0;
                end
                else if (UNIT == UNIT_ELEM) begin
                    unpack_op_flags[0].shift    = state_init.vs1_shift & state_init.gather_fetch;
                    unpack_op_flags[0].hold     = ~state_init.gather_fetch;
                    unpack_op_flags[0].elemwise = '0;
                    unpack_op_flags[0].narrow   = state_init.vs1_narrow;
                    unpack_op_flags[0].sigext   = state_init.mode.elem.sigext;
                    unpack_op_load [1]          = state_init.rs2.vreg & state_init.first_cycle & (state_init.mode.elem.op != ELEM_VRGATHER);
                    unpack_op_flags[2]          = unpack_flags'('0);
                    unpack_op_load [2]          = state_init.gather_fetch & (state_init.mode.elem.op == ELEM_VRGATHER);
                    unpack_op_flags[2].shift    = 1'b1;
                    unpack_op_flags[2].elemwise = '0;
                end
            end
        end
        always_comb begin
            unpack_op_load [OP_CNT-1]          = state_init.v0msk_fetch & state_init_masked;
            unpack_op_vaddr[OP_CNT-1]          = '0;
            unpack_op_flags[OP_CNT-1]          = unpack_flags'('0);
            unpack_op_flags[OP_CNT-1].shift    = (UNIT == UNIT_ELEM) ? 1'b1 : state_init.v0msk_shift;
            unpack_op_flags[OP_CNT-1].elemwise = (UNIT == UNIT_LSU) & (state_init.mode.lsu.stride != LSU_UNITSTRIDE);
            unpack_op_xval [OP_CNT-1]          = '0;
        end
    endgenerate

    localparam bit [2:0]    UNPACK_VPORT_ADDR_ZERO    = (UNIT == UNIT_MUL) ? 3'b100 : 3'b10;
    localparam bit [2:0]    UNPACK_VPORT_BUFFER       = (UNIT == UNIT_MUL) ? 3'b001 : 3'b01;

    localparam bit [3:0]    UNPACK_OP_ADDR_OFFSET_OP0 =  (UNIT == UNIT_ELEM) ? 4'b0100 : '0;
    localparam bit [3:0]    UNPACK_OP_MASK            =  (UNIT == UNIT_MUL ) ? 4'b1000 : (
                                                         (UNIT == UNIT_ELEM) ? 4'b1010 : (
                                                         (UNIT == UNIT_SLD ) ? 4'b10   :
                                                                               4'b100
                                                        ));
    localparam bit [3:0]    UNPACK_OP_XREG            = ((UNIT == UNIT_MUL ) | (UNIT == UNIT_ALU)) ? 4'b0001 : '0;
    localparam bit [3:0]    UNPACK_OP_NARROW          = ((UNIT == UNIT_MUL ) | (UNIT == UNIT_ALU)) ? 4'b0011 : (
                                                        ( UNIT == UNIT_ELEM                      ) ? 4'b0001 :
                                                                                                      '0
                                                        );
    localparam bit [3:0]    UNPACK_OP_ALLOW_ELEMWISE  =  (UNIT == UNIT_LSU ) ? 4'b110  : '0;
    localparam bit [3:0]    UNPACK_OP_ALWAYS_ELEMWISE =  (UNIT == UNIT_LSU ) ? 4'b001  : (
                                                         (UNIT == UNIT_ELEM) ? 4'b1111 :
                                                                                '0
                                                        );
    localparam bit [3:0]    UNPACK_OP_HOLD_FLAG       =  (UNIT == UNIT_ELEM) ? 4'b0001 : '0;

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
        .VPORT_ADDR_ZERO      ( UNPACK_VPORT_ADDR_ZERO[VPORT_CNT-1:0] ),
        .VPORT_BUFFER         ( UNPACK_VPORT_BUFFER   [VPORT_CNT-1:0] ),
        .MAX_OP_W             ( MAX_OP_W                              ),
        .OP_CNT               ( OP_CNT                                ),
        .OP_W                 ( OP_W                                  ),
        .OP_STAGE             ( OP_STAGE                              ),
        .OP_SRC               ( OP_SRC                                ),
        .OP_ADDR_OFFSET_OP0   ( UNPACK_OP_ADDR_OFFSET_OP0[OP_CNT-1:0] ),
        .OP_MASK              ( UNPACK_OP_MASK           [OP_CNT-1:0] ),
        .OP_XREG              ( UNPACK_OP_XREG           [OP_CNT-1:0] ),
        .OP_NARROW            ( UNPACK_OP_NARROW         [OP_CNT-1:0] ),
        .OP_ALLOW_ELEMWISE    ( UNPACK_OP_ALLOW_ELEMWISE [OP_CNT-1:0] ),
        .OP_ALWAYS_ELEMWISE   ( UNPACK_OP_ALWAYS_ELEMWISE[OP_CNT-1:0] ),
        .OP_HOLD_FLAG         ( UNPACK_OP_HOLD_FLAG      [OP_CNT-1:0] ),
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
        .pipe_in_op_load_i    ( unpack_op_load                        ),
        .pipe_in_op_vaddr_i   ( unpack_op_vaddr                       ),
        .pipe_in_op_flags_i   ( unpack_op_flags                       ),
        .pipe_in_op_xval_i    ( unpack_op_xval                        ),
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
                .VREG_W                   ( VREG_W                            ),
                .CFG_VL_W                 ( CFG_VL_W                          ),
                .VMEM_W                   ( MAX_OP_W                          ),
                .CTRL_T                   ( ctrl_t                            ),
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
            logic [COUNTER_W       -1:0] debug_count        = unit_out_ctrl.count.val;
            logic [STRIDE_COUNTER_W-1:0] debug_count_stride = unit_out_ctrl.count_stride;
            always_comb begin
                pack_res_data = '0;
                pack_res_mask = '0;

                pack_res_flags[0] = pack_flags'('0);
                if (unit_out_ctrl.mode.lsu.stride == LSU_UNITSTRIDE) begin
                    pack_res_flags[0].shift    = 1'b1;
                    pack_res_flags[0].elemwise = 1'b0;
                end else begin
                    pack_res_flags[0].shift = DONT_CARE_ZERO ? '0 : 'x;
                    unique case (unit_out_ctrl.mode.lsu.eew)
                        VSEW_8:  pack_res_flags[0].shift =  unit_out_ctrl.count_stride       == '0;
                        VSEW_16: pack_res_flags[0].shift = (unit_out_ctrl.count_stride >> 1) == '0;
                        VSEW_32: pack_res_flags[0].shift = (unit_out_ctrl.count_stride >> 2) == '0;
                        default: ;
                    endcase
                    pack_res_flags[0].elemwise = 1'b1;
                end
                pack_res_store[0]                 = unit_out_ctrl.vd_store;
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
                .VREG_W             ( VREG_W                            ),
                .CFG_VL_W           ( CFG_VL_W                          ),
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
                pack_res_store[0]                 = unit_out_ctrl.vd_store & ~unit_out_ctrl.mode.alu.cmp;
                pack_res_flags[0].shift           = ~unit_out_ctrl.vd_narrow | ~unit_out_ctrl.count.val[0];
                pack_res_flags[0].narrow          = unit_out_ctrl.vd_narrow;
                pack_res_flags[0].saturate        = unit_out_ctrl.mode.alu.sat_res;
                pack_res_flags[0].sig             = unit_out_ctrl.mode.alu.sigext;
                pack_res_valid[0]                 = unit_out_valid;
                pack_res_data [0]                 = unit_out_res_alu;
                pack_res_mask [0][MAX_OP_W/8-1:0] = unit_out_mask;

                pack_res_flags[1]                 = pack_flags'('0);
                pack_res_flags[1].mul_idx         = unit_out_ctrl.count.part.mul;
                pack_res_store[1]                 = unit_out_ctrl.vd_store & unit_out_ctrl.mode.alu.cmp;
                pack_res_valid[1]                 = unit_out_valid;
                pack_res_data [1][MAX_OP_W/8-1:0] = unit_out_res_cmp;
                pack_res_mask [1][MAX_OP_W/8-1:0] = unit_out_mask;
            end
            assign pack_pend_clear     = unit_out_ctrl.mode.alu.cmp ? unit_out_ctrl.last_cycle : unit_out_ctrl.vd_store;
            assign pack_pend_clear_cnt = '0;
            assign unit_out_instr_done = unit_out_ctrl.last_cycle;
        end
        else if (UNIT == UNIT_MUL) begin
            logic [MAX_OP_W  -1:0] unit_out_res;
            logic [MAX_OP_W/8-1:0] unit_out_mask;
            vproc_mul #(
                .VREG_W           ( VREG_W                            ),
                .CFG_VL_W         ( CFG_VL_W                          ),
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
                pack_res_store[0]                 = unit_out_ctrl.vd_store;
                pack_res_valid[0]                 = unit_out_valid;
                pack_res_data [0]                 = unit_out_res;
                pack_res_mask [0][MAX_OP_W/8-1:0] = unit_out_mask;
            end
            assign pack_pend_clear     = unit_out_ctrl.vd_store;
            assign pack_pend_clear_cnt = '0;
            assign unit_out_instr_done = unit_out_ctrl.last_cycle;
        end
        else if (UNIT == UNIT_SLD) begin
            logic [MAX_OP_W  -1:0] unit_out_res;
            logic [MAX_OP_W/8-1:0] unit_out_mask;
            vproc_sld #(
                .VREG_W           ( VREG_W                            ),
                .CFG_VL_W         ( CFG_VL_W                          ),
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
                pack_res_store[0]                 = unit_out_ctrl.vd_store;
                pack_res_valid[0]                 = unit_out_valid;
                pack_res_data [0]                 = unit_out_res;
                pack_res_mask [0][MAX_OP_W/8-1:0] = unit_out_mask;
            end
            assign pack_pend_clear     = unit_out_ctrl.vd_store;
            assign pack_pend_clear_cnt = '0;
            assign unit_out_instr_done = unit_out_ctrl.last_cycle;
        end
        else if (UNIT == UNIT_ELEM) begin
            logic        elem_out_valid;
            logic        elem_out_ready;
            logic        elem_out_xreg_valid;
            logic        unit_out_stall;
            logic        unit_out_res_valid;
            logic [31:0] unit_out_res;
            logic [3 :0] unit_out_mask;
            vproc_elem #(
                .VREG_W                ( VREG_W                  ),
                .CFG_VL_W              ( CFG_VL_W                ),
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
                .pipe_out_ctrl_o       ( unit_out_ctrl           ),
                .pipe_out_xreg_valid_o ( elem_out_xreg_valid     ),
                .pipe_out_xreg_data_o  ( xreg_data_o             ),
                .pipe_out_xreg_addr_o  ( xreg_addr_o             ),
                .pipe_out_res_valid_o  ( unit_out_res_valid      ),
                .pipe_out_res_o        ( unit_out_res            ),
                .pipe_out_mask_o       ( unit_out_mask           )
            );
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
                    VSEW_8:  pack_res_flags[0].shift = unit_out_ctrl.count.val[1:0] == '0;
                    VSEW_16: pack_res_flags[0].shift = unit_out_ctrl.count.val[1:1] == '0;
                    VSEW_32: pack_res_flags[0].shift = 1'b1;
                    default: ;
                endcase
                pack_res_store[0]      = unit_out_ctrl.vd_store;
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


    localparam bit [1:0] PACK_RES_MASK        = (UNIT == UNIT_ALU ) ? 2'b10 : '0;
    localparam bit [1:0] PACK_RES_NARROW      = (UNIT == UNIT_ALU ) ? 2'b01 : '0;
    localparam bit [1:0] PACK_ALLOW_ELEMWISE  = (UNIT == UNIT_LSU ) ? 2'b1  : '0;
    localparam bit [1:0] PACK_ALWAYS_ELEMWISE = (UNIT == UNIT_ELEM) ? 2'b1  : '0;
    vproc_vregpack #(
        .VPORT_W                     ( VREG_W                            ),
        .VADDR_W                     ( 5                                 ),
        .VPORT_WR_ATTEMPTS           ( MAX_WR_ATTEMPTS                   ),
        .VPORT_PEND_CLR_BULK         ( UNIT == UNIT_ELEM                 ),
        .MAX_RES_W                   ( MAX_RES_W                         ),
        .RES_CNT                     ( RES_CNT                           ),
        .RES_W                       ( RES_W                             ),
        .RES_MASK                    ( PACK_RES_MASK       [RES_CNT-1:0] ),
        .RES_XREG                    ( '0                                ),
        .RES_NARROW                  ( PACK_RES_NARROW     [RES_CNT-1:0] ),
        .RES_ALLOW_ELEMWISE          ( PACK_ALLOW_ELEMWISE [RES_CNT-1:0] ),
        .RES_ALWAYS_ELEMWISE         ( PACK_ALWAYS_ELEMWISE[RES_CNT-1:0] ),
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
        .pipe_in_vaddr_i             ( unit_out_ctrl.vd                  ),
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
