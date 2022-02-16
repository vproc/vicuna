// Copyright TU Wien
// Licensed under the Solderpad Hardware License v2.1, see LICENSE.txt for details
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1


module vproc_pipeline #(
        parameter int unsigned          VREG_W           = 128,  // width in bits of vector registers
        parameter int unsigned          VMSK_W           = 16,   // width of vector register masks (= VREG_W / 8)
        parameter int unsigned          CFG_VL_W         = 7,    // width of VL reg in bits (= log2(VREG_W))
        parameter int unsigned          XIF_ID_W         = 3,    // width in bits of instruction IDs
        parameter int unsigned          XIF_ID_CNT       = 8,    // total count of instruction IDs
        parameter vproc_pkg::op_unit    UNIT             = UNIT_ALU,
        parameter int unsigned          OP_W             = 64,   // operand width in bits
        parameter vproc_pkg::mul_type   MUL_TYPE         = vproc_pkg::MUL_GENERIC,
        parameter int unsigned          MAX_WR_ATTEMPTS  = 1,    // max required vregfile write attempts
        parameter bit                   DONT_CARE_ZERO   = 1'b0  // initialize don't care values to zero
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
        output logic [VMSK_W-1:0]       vreg_wr_mask_o,
        output logic                    vreg_wr_en_o
    );

    import vproc_pkg::*;

    if ((OP_W & (OP_W - 1)) != 0 || OP_W < 32 || OP_W >= VREG_W) begin
        $fatal(1, "The vector pipeline operand width OP_W must be at least 32, less than ",
                  "the vector register width VREG_W and a power of two.  ",
                  "The current value of %d is invalid.", OP_W);
    end

    if (MAX_WR_ATTEMPTS < 1 || (1 << (MAX_WR_ATTEMPTS - 1)) > VREG_W / OP_W) begin
        $fatal(1, "The maximum number of write attempts MAX_WR_ATTEMPTS of a vector pipeline ",
                  "must be at least 1 and 2^(MAX_WR_ATTEMPTS-1) must be less than or ",
                  "equal to the ratio of the vector register width vs the operand width ",
                  "of that unit.  ",
                  "MAX_WR_ATTEMPTS is %d and that ratio is %d.",
                  MAX_WR_ATTEMPTS, VREG_W / OP_W);
    end

    // max number of cycles by which a write can be delayed
    localparam int unsigned MAX_WR_DELAY = (1 << (MAX_WR_ATTEMPTS - 1)) - 1;


    ///////////////////////////////////////////////////////////////////////////
    // STATE LOGIC

    localparam int unsigned CYCLES_PER_VREG = VREG_W / OP_W;
    localparam int unsigned COUNTER_W       = $clog2(CYCLES_PER_VREG) + 3;

    typedef union packed {
        logic [COUNTER_W-1:0] val;
        struct packed {
            logic [2:0]           mul; // mul part (vreg index)
            logic [COUNTER_W-4:0] low; // counter part in vreg (vreg pos)
        } part;
    } counter_t;

    typedef struct packed {
        counter_t            count;
        logic                first_cycle;
        logic                last_cycle;
        logic [XIF_ID_W-1:0] id;
        op_mode              mode;
        cfg_vsew             eew;        // effective element width
        cfg_emul             emul;       // effective MUL factor
        cfg_vxrm             vxrm;
        logic [CFG_VL_W-1:0] vl;
        logic                vl_0;
        op_regs              rs1;
        logic                vs1_narrow;
        logic                vs1_fetch;
        logic                vs1_shift;
        op_regs              rs2;
        logic                vs2_narrow;
        logic                vs2_fetch;
        logic                vs2_shift;
        logic                v0msk_fetch;
        logic                v0msk_shift;
        logic                vs3_fetch;
        logic [4:0]          vd;
        logic                vd_narrow;
        logic                vd_store;
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
    end

    logic pipeline_ready;
    always_comb begin
        op_ack_o       = 1'b0;
        state_valid_d  = state_valid_q;
        state_d        = state_q;
        vreg_pend_wr_d = vreg_pend_wr_q & vreg_pend_wr_i;

        if (((~state_valid_q) | (last_cycle & pipeline_ready)) & op_rdy_i) begin
            op_ack_o            = 1'b1;
            state_d.count.val   = '0;
            state_valid_d       = 1'b1;
            state_d.first_cycle = 1'b1;
            state_d.id          = id_i;
            state_d.mode        = mode_i;
            state_d.emul        = emul_i;
            state_d.eew         = vsew_i;
            state_d.vxrm        = vxrm_i;
            state_d.vl          = vl_i;
            state_d.vl_0        = vl_0_i;
            state_d.rs1         = rs1_i;
            state_d.vs1_narrow  = widenarrow_i != OP_SINGLEWIDTH;
            state_d.vs1_fetch   = rs1_i.vreg;
            state_d.vs1_shift   = 1'b1;
            state_d.rs2         = rs2_i;
            state_d.vs2_narrow  = widenarrow_i == OP_WIDENING;
            state_d.vs2_fetch   = (UNIT == UNIT_ALU) ? rs2_i.vreg : 1'b1;
            state_d.vs2_shift   = 1'b1;
            state_d.v0msk_fetch = 1'b1;
            state_d.v0msk_shift = 1'b1;
            state_d.vs3_fetch   = (UNIT == UNIT_MUL) ? (mode_i.mul.op == MUL_VMACC) : '0;
            state_d.vd          = vd_i;
            state_d.vd_narrow   = (UNIT == UNIT_ALU) ? (widenarrow_i == OP_NARROWING) : '0;
            state_d.vd_store    = 1'b0;
            vreg_pend_wr_d      = vreg_pend_wr_i;
        end
        else if (state_valid_q & pipeline_ready) begin
            state_d.count.val   = state_q.count.val + 1;
            state_valid_d       = ~last_cycle;
            state_d.first_cycle = 1'b0;
            state_d.vs1_fetch   = 1'b0;
            state_d.vs2_fetch   = 1'b0;
            state_d.vs3_fetch   = 1'b0;
            if (state_q.count.part.low == '1) begin
                if (state_q.rs1.vreg & (~state_q.vs1_narrow | state_q.count.part.mul[0])) begin
                    state_d.rs1.r.vaddr[2:0] = state_q.rs1.r.vaddr[2:0] + 3'b1;
                    state_d.vs1_fetch        = state_q.rs1.vreg;
                end
                if (~state_q.vs2_narrow | state_q.count.part.mul[0]) begin
                    state_d.rs2.r.vaddr[2:0] = state_q.rs2.r.vaddr[2:0] + 3'b1;
                    state_d.vs2_fetch        = state_q.rs2.vreg;
                end
                if ((UNIT != UNIT_ALU) | (~state_q.mode.alu.cmp & (~state_q.vd_narrow | state_q.count.part.mul[0]))) begin
                    state_d.vd[2:0] = state_q.vd[2:0] + 3'b1;
                end
                state_d.vs3_fetch = (UNIT == UNIT_MUL) ? (state_q.mode.mul.op == MUL_VMACC) : '0;
            end
            state_d.vs1_shift = ~state_q.vs1_narrow | state_q.count.part.low[0];
            state_d.vs2_shift = ~state_q.vs2_narrow | state_q.count.part.low[0];
            state_d.v0msk_fetch = 1'b0;
            unique case (state_q.eew)
                VSEW_8:  state_d.v0msk_shift = 1'b1;
                VSEW_16: state_d.v0msk_shift = state_q.count.val[0];
                VSEW_32: state_d.v0msk_shift = state_q.count.val[1:0] == '1;
                default: ;
            endcase
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
        state_init.vd_store   = (state_q.count.part.low == '1) & (~state_q.vd_narrow | state_q.count.part.mul[0]);

        // Determine whether there is a pending read of v0 as a mask
        state_init_masked = '0;
        unique case (UNIT)
            UNIT_ALU: state_init_masked = state_init.mode.alu.op_mask != ALU_MASK_NONE;
            UNIT_MUL: state_init_masked = state_init.mode.mul.masked;
            default: ;
        endcase
    end
    logic unpack_ready;
    assign pipeline_ready = unpack_ready & ~state_init_stall;

    // Stall vreg reads until pending writes are complete; note that vreg read
    // stalling always happens in the init stage, since otherwise a substantial
    // amount of state would have to be forwarded (such as vreg_pend_wr_q)
    generate
        if (UNIT == UNIT_ALU) begin
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
    endgenerate

    // pending vreg reads
    // Note: The pipeline might stall while reading a vreg, hence a vreg has to
    // be part of the pending reads until the read is complete.
    logic [31:0] pend_vs1, pend_vs2, pend_vs3;
    always_comb begin
        pend_vs1 = DONT_CARE_ZERO ? '0 : 'x;
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
        pend_vs2 = DONT_CARE_ZERO ? '0 : 'x;
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
        if (UNIT == UNIT_ALU) begin
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
    endgenerate


    ///////////////////////////////////////////////////////////////////////////
    // REGISTER READ/WRITE AND UNIT INSTANTIATION

    localparam int unsigned VPORT_CNT =  (UNIT == UNIT_MUL)                        ? 3 : 2;
    localparam int unsigned OP_CNT    = ((UNIT == UNIT_MUL) | (UNIT == UNIT_ELEM)) ? 4 : 3;

    logic        [OP_CNT-1:0]       unpack_op_load;
    logic        [OP_CNT-1:0][4 :0] unpack_op_vaddr;
    unpack_flags [OP_CNT-1:0]       unpack_op_flags;
    logic        [OP_CNT-1:0][31:0] unpack_op_xval;
    always_comb begin
        unpack_op_load [0       ]          = state_init.vs1_fetch;
        unpack_op_vaddr[0       ]          = state_init.rs1.r.vaddr;
        unpack_op_flags[0       ]          = unpack_flags'('0);
        unpack_op_flags[0       ].shift    = state_init.vs1_shift;
        unpack_op_xval [0       ]          = state_init.rs1.r.xval;
        unpack_op_load [1       ]          = state_init.vs2_fetch;
        unpack_op_vaddr[1       ]          = state_init.rs2.r.vaddr;
        unpack_op_flags[1       ]          = unpack_flags'('0);
        unpack_op_flags[1       ].shift    = state_init.vs2_shift;
        unpack_op_xval [1       ]          = '0;
        unpack_op_load [OP_CNT-1]          = state_init.v0msk_fetch & state_init_masked;
        unpack_op_vaddr[OP_CNT-1]          = '0;
        unpack_op_flags[OP_CNT-1]          = unpack_flags'('0);
        unpack_op_flags[OP_CNT-1].shift    = state_init.v0msk_shift;
        unpack_op_flags[OP_CNT-1].elemwise = '0;
        unpack_op_xval [OP_CNT-1]          = '0;
        if (UNIT == UNIT_ALU) begin
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
    end

    localparam int unsigned UNPACK_VPORT_W [3]        = '{VREG_W,VREG_W,VREG_W};
    localparam int unsigned UNPACK_VADDR_W [3]        = '{5,5,5};
    localparam bit [2:0]    UNPACK_VPORT_ADDR_ZERO    = (UNIT == UNIT_MUL) ? 3'b100 : 3'b10;
    localparam bit [2:0]    UNPACK_VPORT_BUFFER       = (UNIT == UNIT_MUL) ? 3'b001 : 3'b01;
    localparam int unsigned UNPACK_OP_W    [4]        = (UNIT == UNIT_MUL) ? '{OP_W,OP_W,OP_W,OP_W/8} : '{OP_W,OP_W,OP_W/8,0};
    localparam int unsigned UNPACK_OP_STAGE[4]        = '{1,2,2,2};
    localparam int unsigned UNPACK_OP_SRC  [4]        = '{0,0,1,2};
    localparam bit [3:0]    UNPACK_OP_ADDR_OFFSET_OP0 =  (UNIT == UNIT_ELEM) ? 4'b0100 : '0;
    localparam bit [3:0]    UNPACK_OP_MASK            =  (UNIT == UNIT_MUL ) ? 4'b1000 : ((UNIT == UNIT_ELEM) ? 4'b1010 : 4'b100);
    localparam bit [3:0]    UNPACK_OP_XREG            = ((UNIT == UNIT_MUL ) | (UNIT == UNIT_ALU)) ? 4'b0001 : '0;
    localparam bit [3:0]    UNPACK_OP_NARROW          = ((UNIT == UNIT_MUL ) | (UNIT == UNIT_ALU)) ? 4'b0011 : '0;
    localparam bit [3:0]    UNPACK_OP_ALLOW_ELEMWISE  =  (UNIT == UNIT_LSU ) ? 4'b110  : '0;
    localparam bit [3:0]    UNPACK_OP_ALWAYS_ELEMWISE =  (UNIT == UNIT_LSU ) ? 4'b001  : ((UNIT == UNIT_ELEM) ? 4'b1111 : '0);
    localparam bit [3:0]    UNPACK_OP_HOLD_FLAG       =  (UNIT == UNIT_ELEM) ? 4'b0001 : '0;

    logic [VPORT_CNT-1:0][4:0]        unpack_vreg_addr;
    logic [VPORT_CNT-1:0][VREG_W-1:0] unpack_vreg_data;
    logic                             unpack_out_valid;
    logic                             unpack_out_ready;
    ctrl_t                            unpack_out_ctrl;
    logic [OP_CNT   -1:0][OP_W  -1:0] unpack_out_ops;
    vproc_vregunpack #(
        .MAX_VPORT_W          ( VREG_W                                ),
        .MAX_VADDR_W          ( 5                                     ),
        .VPORT_CNT            ( VPORT_CNT                             ),
        .VPORT_W              ( UNPACK_VPORT_W                        ),
        .VADDR_W              ( UNPACK_VADDR_W                        ),
        .VPORT_ADDR_ZERO      ( UNPACK_VPORT_ADDR_ZERO[VPORT_CNT-1:0] ),
        .VPORT_BUFFER         ( UNPACK_VPORT_BUFFER   [VPORT_CNT-1:0] ),
        .MAX_OP_W             ( OP_W                                  ),
        .OP_CNT               ( OP_CNT                                ),
        .OP_W                 ( UNPACK_OP_W                           ),
        .OP_STAGE             ( UNPACK_OP_STAGE                       ),
        .OP_SRC               ( UNPACK_OP_SRC                         ),
        .OP_ADDR_OFFSET_OP0   ( UNPACK_OP_ADDR_OFFSET_OP0[OP_CNT-1:0] ),
        .OP_MASK              ( UNPACK_OP_MASK           [OP_CNT-1:0] ),
        .OP_XREG              ( UNPACK_OP_XREG           [OP_CNT-1:0] ),
        .OP_NARROW            ( UNPACK_OP_NARROW         [OP_CNT-1:0] ),
        .OP_ALLOW_ELEMWISE    ( UNPACK_OP_ALLOW_ELEMWISE [OP_CNT-1:0] ),
        .OP_ALWAYS_ELEMWISE   ( UNPACK_OP_ALWAYS_ELEMWISE[OP_CNT-1:0] ),
        .OP_HOLD_FLAG         ( UNPACK_OP_HOLD_FLAG      [OP_CNT-1:0] ),
        .UNPACK_STAGES        ( 3                                     ),
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
        .ctrl_flags_any_o     (                                       ),
        .ctrl_flags_all_o     (                                       )
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

    localparam int unsigned RES_CNT = (UNIT == UNIT_ALU) ? 2 : 1;

    logic                              unit_out_valid;
    logic                              unit_out_ready;
    ctrl_t                             unit_out_ctrl;
    logic      [RES_CNT-1:0]           pack_res_store, pack_res_valid;
    pack_flags [RES_CNT-1:0]           pack_res_flags;
    logic      [RES_CNT-1:0][OP_W-1:0] pack_res_data, pack_res_mask;
    logic                              pack_pend_clear;
    generate
        if (UNIT == UNIT_ALU) begin
            logic [OP_W  -1:0] unit_out_res_alu;
            logic [OP_W/8-1:0] unit_out_res_cmp;
            logic [OP_W/8-1:0] unit_out_mask;
            vproc_alu #(
                .VREG_W             ( VREG_W                        ),
                .CFG_VL_W           ( CFG_VL_W                      ),
                .ALU_OP_W           ( OP_W                          ),
                .CTRL_T             ( ctrl_t                        ),
                .DONT_CARE_ZERO     ( DONT_CARE_ZERO                )
            ) alu (
                .clk_i              ( clk_i                         ),
                .async_rst_ni       ( async_rst_ni                  ),
                .sync_rst_ni        ( sync_rst_ni                   ),
                .pipe_in_valid_i    ( unpack_out_valid              ),
                .pipe_in_ready_o    ( unpack_out_ready              ),
                .pipe_in_ctrl_i     ( unpack_out_ctrl               ),
                .pipe_in_op1_i      ( unpack_out_ops[0]             ),
                .pipe_in_op2_i      ( unpack_out_ops[1]             ),
                .pipe_in_mask_i     ( unpack_out_ops[2][OP_W/8-1:0] ),
                .pipe_out_valid_o   ( unit_out_valid                ),
                .pipe_out_ready_i   ( unit_out_ready                ),
                .pipe_out_ctrl_o    ( unit_out_ctrl                 ),
                .pipe_out_res_alu_o ( unit_out_res_alu              ),
                .pipe_out_res_cmp_o ( unit_out_res_cmp              ),
                .pipe_out_mask_o    ( unit_out_mask                 )
            );
            always_comb begin
                pack_res_data = '0;
                pack_res_mask = '0;

                pack_res_flags[0]             = pack_flags'('0);
                pack_res_store[0]             = unit_out_ctrl.vd_store & ~unit_out_ctrl.mode.alu.cmp;
                pack_res_flags[0].shift       = ~unit_out_ctrl.vd_narrow | ~unit_out_ctrl.count.val[0];
                pack_res_flags[0].narrow      = unit_out_ctrl.vd_narrow;
                pack_res_flags[0].saturate    = unit_out_ctrl.mode.alu.sat_res;
                pack_res_flags[0].sig         = unit_out_ctrl.mode.alu.sigext;
                pack_res_valid[0]             = unit_out_valid;
                pack_res_data [0]             = unit_out_res_alu;
                pack_res_mask [0][OP_W/8-1:0] = unit_out_mask;

                pack_res_flags[1]             = pack_flags'('0);
                pack_res_flags[1].mul_idx     = unit_out_ctrl.count.part.mul;
                pack_res_store[1]             = unit_out_ctrl.vd_store & unit_out_ctrl.mode.alu.cmp;
                pack_res_valid[1]             = unit_out_valid;
                pack_res_data [1][OP_W/8-1:0] = unit_out_res_cmp;
                pack_res_mask [1][OP_W/8-1:0] = unit_out_mask;
            end
            assign pack_pend_clear = unit_out_ctrl.mode.alu.cmp ? unit_out_ctrl.last_cycle : unit_out_ctrl.vd_store;
        end
        else if (UNIT == UNIT_MUL) begin
            logic [OP_W  -1:0] unit_out_res;
            logic [OP_W/8-1:0] unit_out_mask;
            vproc_mul #(
                .VREG_W           ( VREG_W                        ),
                .CFG_VL_W         ( CFG_VL_W                      ),
                .MUL_OP_W         ( OP_W                          ),
                .MUL_TYPE         ( MUL_TYPE                      ),
                .CTRL_T           ( ctrl_t                        ),
                .DONT_CARE_ZERO   ( DONT_CARE_ZERO                )
            ) mul (
                .clk_i            ( clk_i                         ),
                .async_rst_ni     ( async_rst_ni                  ),
                .sync_rst_ni      ( sync_rst_ni                   ),
                .pipe_in_valid_i  ( unpack_out_valid              ),
                .pipe_in_ready_o  ( unpack_out_ready              ),
                .pipe_in_ctrl_i   ( unpack_out_ctrl               ),
                .pipe_in_op1_i    ( unpack_out_ops[0]             ),
                .pipe_in_op2_i    ( unpack_out_ops[1]             ),
                .pipe_in_op3_i    ( unpack_out_ops[2]             ),
                .pipe_in_mask_i   ( unpack_out_ops[3][OP_W/8-1:0] ),
                .pipe_out_valid_o ( unit_out_valid                ),
                .pipe_out_ready_i ( unit_out_ready                ),
                .pipe_out_ctrl_o  ( unit_out_ctrl                 ),
                .pipe_out_res_o   ( unit_out_res                  ),
                .pipe_out_mask_o  ( unit_out_mask                 )
            );
            always_comb begin
                pack_res_data = '0;
                pack_res_mask = '0;

                pack_res_flags[0]             = pack_flags'('0);
                pack_res_store[0]             = unit_out_ctrl.vd_store;
                pack_res_valid[0]             = unit_out_valid;
                pack_res_data [0]             = unit_out_res;
                pack_res_mask [0][OP_W/8-1:0] = unit_out_mask;
            end
            assign pack_pend_clear = unit_out_ctrl.vd_store;
        end
    endgenerate

    localparam int unsigned PACK_RES_W[2] = '{OP_W, OP_W/8};
    localparam bit [1:0] PACK_RES_MASK    = (UNIT == UNIT_ALU) ? 2'b10 : '0;
    localparam bit [1:0] PACK_RES_NARROW  = (UNIT == UNIT_ALU) ? 2'b01 : '0;
    vproc_vregpack #(
        .VPORT_W                     ( VREG_W                       ),
        .VADDR_W                     ( 5                            ),
        .VPORT_WR_ATTEMPTS           ( MAX_WR_ATTEMPTS              ),
        .VPORT_PEND_CLR_BULK         ( '0                           ),
        .MAX_RES_W                   ( OP_W                         ),
        .RES_CNT                     ( RES_CNT                      ),
        .RES_W                       ( PACK_RES_W                   ),
        .RES_MASK                    ( PACK_RES_MASK  [RES_CNT-1:0] ),
        .RES_XREG                    ( '0                           ),
        .RES_NARROW                  ( PACK_RES_NARROW[RES_CNT-1:0] ),
        .RES_ALLOW_ELEMWISE          ( '0                           ),
        .RES_ALWAYS_ELEMWISE         ( '0                           ),
        .FLAGS_T                     ( pack_flags                   ),
        .INSTR_ID_W                  ( XIF_ID_W                     ),
        .INSTR_ID_CNT                ( XIF_ID_CNT                   ),
        .DONT_CARE_ZERO              ( DONT_CARE_ZERO               )
    ) pack (
        .clk_i                       ( clk_i                        ),
        .async_rst_ni                ( async_rst_ni                 ),
        .sync_rst_ni                 ( sync_rst_ni                  ),
        .pipe_in_valid_i             ( unit_out_valid               ),
        .pipe_in_ready_o             ( unit_out_ready               ),
        .pipe_in_instr_id_i          ( unit_out_ctrl.id             ),
        .pipe_in_eew_i               ( unit_out_ctrl.eew            ),
        .pipe_in_vaddr_i             ( unit_out_ctrl.vd             ),
        .pipe_in_res_store_i         ( pack_res_store               ),
        .pipe_in_res_valid_i         ( pack_res_valid               ),
        .pipe_in_res_flags_i         ( pack_res_flags               ),
        .pipe_in_res_data_i          ( pack_res_data                ),
        .pipe_in_res_mask_i          ( pack_res_mask                ),
        .pipe_in_pend_clr_i          ( pack_pend_clear              ),
        .pipe_in_pend_clr_cnt_i      ( '0                           ),
        .pipe_in_instr_done_i        ( unit_out_ctrl.last_cycle     ),
        .vreg_wr_valid_o             ( vreg_wr_en_o                 ),
        .vreg_wr_ready_i             ( 1'b1                         ),
        .vreg_wr_addr_o              ( vreg_wr_addr_o               ),
        .vreg_wr_be_o                ( vreg_wr_mask_o               ),
        .vreg_wr_data_o              ( vreg_wr_o                    ),
        .pending_vreg_reads_i        ( vreg_pend_rd_i               ),
        .clear_pending_vreg_writes_o ( clear_wr_hazards_o           ),
        .instr_spec_i                ( instr_spec_i                 ),
        .instr_killed_i              ( instr_killed_i               ),
        .instr_done_valid_o          ( instr_done_valid_o           ),
        .instr_done_id_o             ( instr_done_id_o              )
    );


`ifdef VPROC_SVA
`include "vproc_pipeline_sva.svh"
`endif

endmodule
