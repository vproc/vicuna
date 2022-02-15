// Copyright TU Wien
// Licensed under the Solderpad Hardware License v2.1, see LICENSE.txt for details
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1


`include "vproc_vregshift.svh"

module vproc_mul #(
        parameter int unsigned        VREG_W          = 128,  // width in bits of vector registers
        parameter int unsigned        VMSK_W          = 16,   // width of vector register masks (= VREG_W / 8)
        parameter int unsigned        CFG_VL_W        = 7,    // width of VL reg in bits (= log2(VREG_W))
        parameter int unsigned        MUL_OP_W        = 64,   // MUL unit operand width in bits
        parameter int unsigned        XIF_ID_W        = 3,    // width in bits of instruction IDs
        parameter int unsigned        XIF_ID_CNT      = 8,    // total count of instruction IDs
        parameter int unsigned        MAX_WR_ATTEMPTS = 1,    // max required vregfile write attempts
        parameter vproc_pkg::mul_type MUL_TYPE        = vproc_pkg::MUL_GENERIC,
        parameter bit                 BUF_VREG        = 1'b1, // insert pipeline stage after vreg read
        parameter bit                 BUF_OPERANDS    = 1'b1, // insert pipeline stage after operand extraction
        parameter bit                 BUF_MUL_IN      = 1'b1, // insert pipeline stage before HW multiplication
        parameter bit                 BUF_MUL_OUT     = 1'b1, // insert pipeline stage after HW multiplication
        parameter bit                 BUF_RESULTS     = 1'b1, // insert pipeline stage after computing result
        parameter bit                 DONT_CARE_ZERO  = 1'b0  // initialize don't care values to zero
    )(
        input  logic                  clk_i,
        input  logic                  async_rst_ni,
        input  logic                  sync_rst_ni,

        input  logic [XIF_ID_W-1:0]   id_i,
        input  vproc_pkg::cfg_vsew    vsew_i,
        input  vproc_pkg::cfg_emul    emul_i,
        input  vproc_pkg::cfg_vxrm    vxrm_i,
        input  logic [CFG_VL_W-1:0]   vl_i,
        input  logic                  vl_0_i,

        input  logic                  op_rdy_i,
        output logic                  op_ack_o,

        input  vproc_pkg::op_mode_mul mode_i,
        input                         widening_i,
        input  vproc_pkg::op_regs     rs1_i,
        input  vproc_pkg::op_regs     rs2_i,
        input  logic [4:0]            vd_i,

        input  logic [31:0]           vreg_pend_wr_i,
        output logic [31:0]           vreg_pend_rd_o,
        input  logic [31:0]           vreg_pend_rd_i,

        output logic [31:0]           clear_wr_hazards_o,

        input  logic [XIF_ID_CNT-1:0] instr_spec_i,
        input  logic [XIF_ID_CNT-1:0] instr_killed_i,
        output logic                  instr_done_valid_o,
        output logic [XIF_ID_W-1:0]   instr_done_id_o,

        // connections to register file:
        input  logic [VREG_W-1:0]     vreg_mask_i,
        input  logic [VREG_W-1:0]     vreg_rd_i,
        input  logic [VREG_W-1:0]     vreg_rd3_i,
        output logic [4:0]            vreg_rd_addr_o,
        output logic [4:0]            vreg_rd3_addr_o,
        output logic [VREG_W-1:0]     vreg_wr_o,
        output logic [4:0]            vreg_wr_addr_o,
        output logic [VMSK_W-1:0]     vreg_wr_mask_o,
        output logic                  vreg_wr_en_o
    );

    import vproc_pkg::*;

    if ((MUL_OP_W & (MUL_OP_W - 1)) != 0 || MUL_OP_W < 32 || MUL_OP_W >= VREG_W) begin
        $fatal(1, "The vector MUL operand width MUL_OP_W must be at least 32, less than ",
                  "the vector register width VREG_W and a power of two.  ",
                  "The current value of %d is invalid.", MUL_OP_W);
    end

    if (MAX_WR_ATTEMPTS < 1 || (1 << (MAX_WR_ATTEMPTS - 1)) > VREG_W / MUL_OP_W) begin
        $fatal(1, "The maximum number of write attempts MAX_WR_ATTEMPTS of a unit ",
                  "must be at least 1 and 2^(MAX_WR_ATTEMPTS-1) must be less than or ",
                  "equal to the ratio of the vector register width vs the operand width ",
                  "of that unit.  ",
                  "For the vector MUL unit MAX_WR_ATTEMPTS is %d and that ratio is %d.",
                  MAX_WR_ATTEMPTS, VREG_W / MUL_OP_W);
    end

    // max number of cycles by which a write can be delayed
    localparam int unsigned MAX_WR_DELAY = (1 << (MAX_WR_ATTEMPTS - 1)) - 1;


    ///////////////////////////////////////////////////////////////////////////
    // MUL STATE:

    localparam int unsigned MUL_CYCLES_PER_VREG = VREG_W / MUL_OP_W;
    localparam int unsigned MUL_COUNTER_W      = $clog2(MUL_CYCLES_PER_VREG) + 3;

    typedef union packed {
        logic [MUL_COUNTER_W-1:0] val;
        struct packed {
            logic [2:0]               mul; // mul part (vreg index)
            logic [MUL_COUNTER_W-4:0] low; // counter part in vreg (vreg pos)
        } part;
    } mul_counter;

    typedef struct packed {
        mul_counter          count;
        logic                first_cycle;
        logic                last_cycle;
        logic [XIF_ID_W-1:0] id;
        op_mode_mul          mode;
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
        logic                vd_store;
    } mul_state;

    logic        state_valid_q,  state_valid_d;
    mul_state    state_q,        state_d;
    logic [31:0] vreg_pend_wr_q, vreg_pend_wr_d; // local copy of global vreg write mask
    always_ff @(posedge clk_i or negedge async_rst_ni) begin : vproc_mul_state_valid
        if (~async_rst_ni) begin
            state_valid_q <= 1'b0;
        end
        else if (~sync_rst_ni) begin
            state_valid_q <= 1'b0;
        end else begin
            state_valid_q <= state_valid_d;
        end
    end
    always_ff @(posedge clk_i) begin : vproc_mul_state
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
            state_d.vs1_narrow  = widening_i;
            state_d.vs1_fetch   = rs1_i.vreg;
            state_d.vs1_shift   = 1'b1;
            state_d.rs2         = rs2_i;
            state_d.vs2_narrow  = widening_i;
            state_d.vs2_fetch   = 1'b1;
            state_d.vs2_shift   = 1'b1;
            state_d.v0msk_fetch = 1'b1;
            state_d.v0msk_shift = 1'b1;
            state_d.vs3_fetch   = mode_i.op == MUL_VMACC;
            state_d.vd          = vd_i;
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
                    state_d.vs2_fetch        = 1'b1;
                end
                state_d.vs3_fetch = state_q.mode.op == MUL_VMACC;
                state_d.vd[2:0]   = state_q.vd[2:0] + 3'b1;
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
    // MUL PIPELINE BUFFERS:

    // pass state information along pipeline:
    logic                       state_ex1_ready,                      state_ex2_ready,   state_ex3_ready,   state_res_ready,   state_vd_ready;
    logic     state_init_stall;
    logic     state_init_valid, state_ex1_valid_q, state_ex1_valid_d, state_ex2_valid_q, state_ex3_valid_q, state_res_valid_q;
    mul_state state_init,       state_ex1_q,       state_ex1_d,       state_ex2_q,       state_ex3_q,       state_res_q;
    always_comb begin
        state_init_valid      = state_valid_q;
        state_init            = state_q;
        state_init.last_cycle = state_valid_q & last_cycle;
        state_init.vd_store   = state_q.count.part.low == '1;
    end
    logic unpack_ready;
    assign pipeline_ready = unpack_ready & ~state_init_stall;

    // operands and result:
    logic [MUL_OP_W  -1:0] operand1_q,     operand1_d;
    logic [MUL_OP_W  -1:0] operand2_q,     operand2_d;
    logic [MUL_OP_W/8-1:0] operand_mask_q, operand_mask_d;
    logic [MUL_OP_W  -1:0] accumulator1_q, accumulator1_d;
    logic [MUL_OP_W  -1:0] accumulator2_q, accumulator2_d;
    logic [MUL_OP_W  -1:0] result_q,       result_d;
    logic [MUL_OP_W/8-1:0] result_mask1_q, result_mask1_d;
    logic [MUL_OP_W/8-1:0] result_mask2_q, result_mask2_d;
    logic [MUL_OP_W/8-1:0] result_mask3_q, result_mask3_d;

    generate
        if (BUF_OPERANDS) begin
            always_ff @(posedge clk_i or negedge async_rst_ni) begin : vproc_mul_stage_ex1_valid
                if (~async_rst_ni) begin
                    state_ex1_valid_q <= 1'b0;
                end
                else if (~sync_rst_ni) begin
                    state_ex1_valid_q <= 1'b0;
                end
                else if (state_ex1_ready) begin
                    state_ex1_valid_q <= state_ex1_valid_d;
                end
            end
            always_ff @(posedge clk_i) begin : vproc_mul_stage_ex1
                if (state_ex1_ready & state_ex1_valid_d) begin
                    state_ex1_q    <= state_ex1_d;
                    operand1_q     <= operand1_d;
                    operand2_q     <= operand2_d;
                    operand_mask_q <= operand_mask_d;
                    accumulator1_q <= accumulator1_d;
                end
            end
            assign state_ex1_ready = ~state_ex1_valid_q | state_ex2_ready;
        end else begin
            always_comb begin
                state_ex1_valid_q = state_ex1_valid_d;
                state_ex1_q       = state_ex1_d;
                operand1_q        = operand1_d;
                operand2_q        = operand2_d;
                operand_mask_q    = operand_mask_d;
                accumulator1_q    = accumulator1_d;
            end
            assign state_ex1_ready = state_ex2_ready;
        end

        if (BUF_MUL_IN) begin
            always_ff @(posedge clk_i or negedge async_rst_ni) begin : vproc_mul_stage_ex2_valid
                if (~async_rst_ni) begin
                    state_ex2_valid_q <= 1'b0;
                end
                else if (~sync_rst_ni) begin
                    state_ex2_valid_q <= 1'b0;
                end
                else if (state_ex2_ready) begin
                    state_ex2_valid_q <= state_ex1_valid_q;
                end
            end
            always_ff @(posedge clk_i) begin : vproc_mul_stage_ex2
                if (state_ex2_ready & state_ex1_valid_q) begin
                    state_ex2_q    <= state_ex1_q;
                    accumulator2_q <= accumulator2_d;
                    result_mask1_q <= result_mask1_d;
                end
            end
            assign state_ex2_ready = ~state_ex2_valid_q | state_ex3_ready;
        end else begin
            always_comb begin
                state_ex2_valid_q = state_ex1_valid_q;
                state_ex2_q       = state_ex1_q;
                accumulator2_q    = accumulator2_d;
                result_mask1_q    = result_mask1_d;
            end
            assign state_ex2_ready = state_ex3_ready;
        end

        if (BUF_MUL_OUT) begin
            always_ff @(posedge clk_i or negedge async_rst_ni) begin : vproc_mul_stage_ex3_valid
                if (~async_rst_ni) begin
                    state_ex3_valid_q <= 1'b0;
                end
                else if (~sync_rst_ni) begin
                    state_ex3_valid_q <= 1'b0;
                end
                else if (state_ex3_ready) begin
                    state_ex3_valid_q <= state_ex2_valid_q;
                end
            end
            always_ff @(posedge clk_i) begin : vproc_mul_stage_ex3
                if (state_ex3_ready & state_ex2_valid_q) begin
                    state_ex3_q    <= state_ex2_q;
                    result_mask2_q <= result_mask2_d;
                end
            end
            assign state_ex3_ready = ~state_ex3_valid_q | state_res_ready;
        end else begin
            always_comb begin
                state_ex3_valid_q = state_ex2_valid_q;
                state_ex3_q       = state_ex2_q;
                result_mask2_q    = result_mask2_d;
            end
            assign state_ex3_ready = state_res_ready;
        end

        if (BUF_RESULTS) begin
            always_ff @(posedge clk_i or negedge async_rst_ni) begin : vproc_mul_stage_res_valid
                if (~async_rst_ni) begin
                    state_res_valid_q <= 1'b0;
                end
                else if (~sync_rst_ni) begin
                    state_res_valid_q <= 1'b0;
                end
                else if (state_res_ready) begin
                    state_res_valid_q <= state_ex3_valid_q;
                end
            end
            always_ff @(posedge clk_i) begin : vproc_mul_stage_res
                if (state_res_ready & state_ex3_valid_q) begin
                    state_res_q    <= state_ex3_q;
                    result_q       <= result_d;
                    result_mask3_q <= result_mask3_d;
                end
            end
            assign state_res_ready = ~state_res_valid_q | state_vd_ready;
        end else begin
            always_comb begin
                state_res_valid_q = state_ex3_valid_q;
                state_res_q       = state_ex3_q;
                result_q          = result_d;
                result_mask3_q    = result_mask3_d;
            end
            assign state_res_ready = state_vd_ready;
        end
    endgenerate

    // Stall vreg reads until pending writes are complete; note that vreg read
    // stalling always happens in the init stage, since otherwise a substantial
    // amount of state would have to be forwarded (such as vreg_pend_wr_q)
    assign state_init_stall = (state_init.vs1_fetch   & vreg_pend_wr_q[state_init.rs1.r.vaddr]) |
                              (state_init.vs2_fetch   & vreg_pend_wr_q[state_init.rs2.r.vaddr]) |
                              (state_init.vs3_fetch   & vreg_pend_wr_q[state_init.vd         ]) |
                              (state_init.v0msk_fetch & state_init.mode.masked & vreg_pend_wr_q[0]);

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
    // Note: vs2 is read in the second cycle; vs3 and the v0 mask have no extra
    // buffer and are always read in state_vs1
    logic [31:0] unpack_pend_rd;
    assign vreg_pend_rd_o = ((
            ((state_init_valid & state_init.rs1.vreg              ) ? pend_vs1                        : '0) |
            ((state_init_valid                                    ) ? pend_vs2                        : '0) |
            ((state_init_valid & (state_init.mode.op == MUL_VMACC)) ? pend_vs3                        : '0) |
            ((state_init_valid & state_init.v0msk_fetch           ) ? {31'b0, state_init.mode.masked} : '0)
        ) & ~vreg_pend_wr_q) |
    unpack_pend_rd;


    ///////////////////////////////////////////////////////////////////////////
    // MUL REGISTER READ/WRITE:

    unpack_flags [3:0]       unpack_op_flags;
    logic        [3:0][4 :0] unpack_op_vaddr;
    logic        [3:0][31:0] unpack_op_xval;
    always_comb begin
        unpack_op_flags  [0]          = unpack_flags'('0);
        unpack_op_flags  [0].shift    = state_init.vs1_shift;
        unpack_op_flags  [0].load     = state_init.vs1_fetch;
        unpack_op_flags  [0].vreg     = state_init.rs1.vreg;
        unpack_op_flags  [0].elemwise = '0;
        unpack_op_flags  [0].narrow   = state_init.vs1_narrow;
        unpack_op_flags  [0].sigext   = state_init.mode.op1_signed;
        unpack_op_vaddr  [0]          = state_init.rs1.r.vaddr;
        unpack_op_xval   [0]          = state_init.rs1.r.xval;
        unpack_op_flags  [1]          = unpack_flags'('0);
        unpack_op_flags  [1].shift    = state_init.vs2_shift;
        unpack_op_flags  [1].load     = state_init.vs2_fetch;
        unpack_op_flags  [1].elemwise = '0;
        unpack_op_flags  [1].narrow   = state_init.vs2_narrow;
        unpack_op_flags  [1].sigext   = state_init.mode.op2_signed;
        unpack_op_vaddr  [1]          = state_init.mode.op2_is_vd ? state_init.vd : state_init.rs2.r.vaddr;
        unpack_op_xval   [1]          = '0;
        unpack_op_flags  [2]          = unpack_flags'('0);
        unpack_op_flags  [2].shift    = 1'b1;
        unpack_op_flags  [2].load     = state_init.vs3_fetch;
        unpack_op_flags  [2].elemwise = '0;
        unpack_op_flags  [2].narrow   = '0;
        unpack_op_flags  [2].sigext   = '0;
        unpack_op_vaddr  [2]          = state_init.mode.op2_is_vd ? state_init.rs2.r.vaddr : state_init.vd;
        unpack_op_xval   [2]          = '0;
        unpack_op_flags  [3]          = unpack_flags'('0);
        unpack_op_flags  [3].shift    = state_init.v0msk_shift;
        unpack_op_flags  [3].load     = state_init.v0msk_fetch & state_init.mode.masked;
        unpack_op_flags  [3].elemwise = '0;
        unpack_op_flags  [3].narrow   = '0;
        unpack_op_flags  [3].sigext   = '0;
        unpack_op_vaddr  [3]          = '0;
        unpack_op_xval   [3]          = '0;
    end

    localparam int unsigned UNPACK_VPORT_W [3] = '{VREG_W,VREG_W,VREG_W};
    localparam int unsigned UNPACK_VADDR_W [3] = '{5,5,5};
    localparam int unsigned UNPACK_OP_W    [4] = '{MUL_OP_W,MUL_OP_W,MUL_OP_W,MUL_OP_W/8};
    localparam int unsigned UNPACK_OP_STAGE[4] = '{1,2,2,2};
    localparam int unsigned UNPACK_OP_SRC  [4] = '{0,0,1,2};

    logic [3:0][MUL_OP_W-1:0] unpack_ops;
    logic [2:0][4:0]          unpack_vreg_addr;
    logic [2:0][VREG_W-1:0]   unpack_vreg_data;
    vproc_vregunpack #(
        .MAX_VPORT_W          ( VREG_W                               ),
        .MAX_VADDR_W          ( 5                                    ),
        .VPORT_CNT            ( 3                                    ),
        .VPORT_W              ( UNPACK_VPORT_W                       ),
        .VADDR_W              ( UNPACK_VADDR_W                       ),
        .VPORT_ADDR_ZERO      ( 3'b100                               ),
        .VPORT_BUFFER         ( 3'b001                               ),
        .MAX_OP_W             ( MUL_OP_W                             ),
        .OP_CNT               ( 4                                    ),
        .OP_W                 ( UNPACK_OP_W                          ),
        .OP_STAGE             ( UNPACK_OP_STAGE                      ),
        .OP_SRC               ( UNPACK_OP_SRC                        ),
        .OP_ADDR_OFFSET_OP0   ( 4'b0000                              ),
        .OP_MASK              ( 4'b1000                              ),
        .OP_XREG              ( 4'b0001                              ),
        .OP_NARROW            ( 4'b0011                              ),
        .OP_ALLOW_ELEMWISE    ( 4'b0000                              ),
        .OP_ALWAYS_ELEMWISE   ( 4'b0000                              ),
        .OP_HOLD_FLAG         ( 4'b0000                              ),
        .UNPACK_STAGES        ( 3                                    ),
        .FLAGS_T              ( unpack_flags                         ),
        .CTRL_DATA_W          ( $bits(mul_state)                     ),
        .DONT_CARE_ZERO       ( DONT_CARE_ZERO                       )
    ) mul_unpack (
        .clk_i                ( clk_i                                ),
        .async_rst_ni         ( async_rst_ni                         ),
        .sync_rst_ni          ( sync_rst_ni                          ),
        .vreg_rd_addr_o       ( unpack_vreg_addr                     ),
        .vreg_rd_data_i       ( unpack_vreg_data                     ),
        .pipe_in_valid_i      ( state_init_valid & ~state_init_stall ),
        .pipe_in_ready_o      ( unpack_ready                         ),
        .pipe_in_ctrl_i       ( state_init                           ),
        .pipe_in_eew_i        ( state_init.eew                       ),
        .pipe_in_op_flags_i   ( unpack_op_flags                      ),
        .pipe_in_op_vaddr_i   ( unpack_op_vaddr                      ),
        .pipe_in_op_xval_i    ( unpack_op_xval                       ),
        .pipe_out_valid_o     ( state_ex1_valid_d                    ),
        .pipe_out_ready_i     ( state_ex1_ready                      ),
        .pipe_out_ctrl_o      ( state_ex1_d                          ),
        .pipe_out_op_data_o   ( unpack_ops                           ),
        .pending_vreg_reads_o ( unpack_pend_rd                       ),
        .stage_valid_any_o    (                                      ),
        .ctrl_flags_any_o     (                                      ),
        .ctrl_flags_all_o     (                                      )
    );
    assign vreg_rd_addr_o  = unpack_vreg_addr[0];
    assign vreg_rd3_addr_o = unpack_vreg_addr[1];
    always_comb begin
        unpack_vreg_data[0] = vreg_rd_i;
        unpack_vreg_data[1] = vreg_rd3_i;
        unpack_vreg_data[2] = vreg_mask_i;
    end
    assign operand1_d     = unpack_ops[0];
    assign operand2_d     = unpack_ops[1];
    assign accumulator1_d = unpack_ops[2];
    assign operand_mask_d = unpack_ops[3][MUL_OP_W/8-1:0];

    // result byte mask:
    logic [VREG_W-1:0] vl_mask;
    assign vl_mask        = state_ex1_q.vl_0 ? {VREG_W{1'b0}} : ({VREG_W{1'b1}} >> (~state_ex1_q.vl));
    assign result_mask1_d = (state_ex1_q.mode.masked ? operand_mask_q : {(MUL_OP_W/8){1'b1}}) & vl_mask[state_ex1_q.count.val*MUL_OP_W/8 +: MUL_OP_W/8];

    assign result_mask2_d = result_mask1_q;
    assign result_mask3_d = result_mask2_q;

    logic      [0:0] pack_res_store, pack_res_valid;
    pack_flags [0:0] pack_res_flags;
    always_comb begin
        pack_res_flags[0] = pack_flags'('0);
        pack_res_store[0] = state_res_q.vd_store;
        pack_res_valid[0] = state_res_valid_q;
    end
    logic [0:0][MUL_OP_W-1:0] pack_res_data, pack_res_mask;
    always_comb begin
        pack_res_data[0]                 = result_q;
        pack_res_mask                    = '0;
        pack_res_mask[0][MUL_OP_W/8-1:0] = result_mask3_q;
    end
    localparam int unsigned PACK_RES_W[1] = '{MUL_OP_W};
    vproc_vregpack #(
        .VPORT_W                     ( VREG_W                 ),
        .VADDR_W                     ( 5                      ),
        .VPORT_WR_ATTEMPTS           ( MAX_WR_ATTEMPTS        ),
        .VPORT_PEND_CLR_BULK         ( '0                     ),
        .MAX_RES_W                   ( MUL_OP_W               ),
        .RES_CNT                     ( 1                      ),
        .RES_W                       ( PACK_RES_W             ),
        .RES_MASK                    ( '0                     ),
        .RES_XREG                    ( '0                     ),
        .RES_NARROW                  ( '0                     ),
        .RES_ALLOW_ELEMWISE          ( '0                     ),
        .RES_ALWAYS_ELEMWISE         ( '0                     ),
        .FLAGS_T                     ( pack_flags             ),
        .INSTR_ID_W                  ( XIF_ID_W               ),
        .INSTR_ID_CNT                ( XIF_ID_CNT             ),
        .DONT_CARE_ZERO              ( DONT_CARE_ZERO         )
    ) mul_pack (
        .clk_i                       ( clk_i                  ),
        .async_rst_ni                ( async_rst_ni           ),
        .sync_rst_ni                 ( sync_rst_ni            ),
        .pipe_in_valid_i             ( state_res_valid_q      ),
        .pipe_in_ready_o             ( state_vd_ready         ),
        .pipe_in_instr_id_i          ( state_res_q.id         ),
        .pipe_in_eew_i               ( state_res_q.eew        ),
        .pipe_in_vaddr_i             ( state_res_q.vd         ),
        .pipe_in_res_store_i         ( pack_res_store         ),
        .pipe_in_res_valid_i         ( pack_res_valid         ),
        .pipe_in_res_flags_i         ( pack_res_flags         ),
        .pipe_in_res_data_i          ( pack_res_data          ),
        .pipe_in_res_mask_i          ( pack_res_mask          ),
        .pipe_in_pend_clr_i          ( state_res_q.vd_store   ),
        .pipe_in_pend_clr_cnt_i      ( '0                     ),
        .pipe_in_instr_done_i        ( state_res_q.last_cycle ),
        .vreg_wr_valid_o             ( vreg_wr_en_o           ),
        .vreg_wr_ready_i             ( 1'b1                   ),
        .vreg_wr_addr_o              ( vreg_wr_addr_o         ),
        .vreg_wr_be_o                ( vreg_wr_mask_o         ),
        .vreg_wr_data_o              ( vreg_wr_o              ),
        .pending_vreg_reads_i        ( vreg_pend_rd_i         ),
        .clear_pending_vreg_writes_o ( clear_wr_hazards_o     ),
        .instr_spec_i                ( instr_spec_i           ),
        .instr_killed_i              ( instr_killed_i         ),
        .instr_done_valid_o          ( instr_done_valid_o     ),
        .instr_done_id_o             ( instr_done_id_o        )
    );


    ///////////////////////////////////////////////////////////////////////////
    // MUL ARITHMETIC:

    logic [MUL_OP_W/8-1:0] op1_signs, op2_signs;
    always_comb begin
        op1_signs = DONT_CARE_ZERO ? '0 : 'x;
        op2_signs = DONT_CARE_ZERO ? '0 : 'x;
        for (int i = 0; i < MUL_OP_W/8; i++) begin
            op1_signs[i] = state_ex1_q.mode.op1_signed & operand1_q[8*i+7];
            op2_signs[i] = state_ex1_q.mode.op2_signed & operand2_q[8*i+7];
        end
    end

    logic ex1_vsew_8, ex1_vsew_32;
    always_comb begin
        ex1_vsew_8  = DONT_CARE_ZERO ? '0 : 'x;
        ex1_vsew_32 = DONT_CARE_ZERO ? '0 : 'x;
        unique case (state_ex1_q.eew)
            VSEW_8:  ex1_vsew_8 = 1'b1;
            VSEW_16: ex1_vsew_8 = 1'b0;
            VSEW_32: ex1_vsew_8 = 1'b0;
            default: ;
        endcase
        unique case (state_ex1_q.eew)
            VSEW_8:  ex1_vsew_32 = 1'b0;
            VSEW_16: ex1_vsew_32 = 1'b0;
            VSEW_32: ex1_vsew_32 = 1'b1;
            default: ;
        endcase
    end

    logic [(MUL_OP_W/8)*17-1:0] mul_op1, mul_op2;
    always_comb begin
        mul_op1 = DONT_CARE_ZERO ? '0 : 'x;
        for (int i = 0; i < MUL_OP_W / 32; i++) begin
            mul_op1[68*i +: 68] = {
                // VSEW_8: byte 3, VSEW_32: upper halfword
                op1_signs[4*i+3]               , ~ex1_vsew_32 ? {{8{op1_signs[4*i+3]}},  operand1_q[32*i+24 +: 8]} : operand1_q[32*i+16 +: 16],
                // VSEW_8: byte 2, VSEW_16 and VSEW_32: upper halfword
                op1_signs[4*i+3]               ,  ex1_vsew_8  ?  {8{op1_signs[4*i+2]}} : operand1_q[32*i+24 +: 8],   operand1_q[32*i+16 +: 8 ],
                // VSEW_8: byte 1, VSEW_32: lower halfword
                1'b0                           , ~ex1_vsew_32 ? {{8{op1_signs[4*i+1]}},  operand1_q[32*i+8  +: 8]} : operand1_q[32*i    +: 16],
                // VSEW_8: byte 0, VSEW_16 and VSEW_32: lower halfword
                ~ex1_vsew_32 & op1_signs[4*i+1],  ex1_vsew_8  ?  {8{op1_signs[4*i  ]}} : operand1_q[32*i+8  +: 8],   operand1_q[32*i    +: 8 ]
            };
        end
        mul_op2 = DONT_CARE_ZERO ? '0 : 'x;
        for (int i = 0; i < MUL_OP_W / 32; i++) begin
            mul_op2[68*i +: 68] = {
                // VSEW_8: byte 3, VSEW_32: lower halfword
                1'b0                           , ~ex1_vsew_32 ? {{8{op2_signs[4*i+3]}},  operand2_q[32*i+24 +: 8]} : operand2_q[32*i    +: 16],
                // VSEW_8: byte 2, VSEW_16 and VSEW_32: upper halfword
                op2_signs[4*i+3]               ,  ex1_vsew_8  ?  {8{op2_signs[4*i+2]}} : operand2_q[32*i+24 +: 8],   operand2_q[32*i+16 +: 8 ],
                // VSEW_8: byte 1, VSEW_32: upper halfword
                op2_signs[4*i+3]               , ~ex1_vsew_32 ? {{8{op2_signs[4*i+1]}},  operand2_q[32*i+8  +: 8]} : operand2_q[32*i+16 +: 16],
                // VSEW_8: byte 0, VSEW_16 and VSEW_32: lower halfword
                ~ex1_vsew_32 & op2_signs[4*i+1],  ex1_vsew_8  ?  {8{op2_signs[4*i  ]}} : operand2_q[32*i+8  +: 8],   operand2_q[32*i    +: 8 ]
            };
        end
    end

    always_comb begin
        accumulator2_d = DONT_CARE_ZERO ? '0 : 'x;
        unique case (state_ex1_q.mode.op)
            MUL_VSMUL: begin
                unique case (state_ex1_q.eew)
                    VSEW_8:  accumulator2_d = {MUL_OP_W/32{32'h40404040}};
                    VSEW_16: accumulator2_d = {MUL_OP_W/32{32'h40004000}};
                    VSEW_32: accumulator2_d = {MUL_OP_W/32{32'h40000000}};
                    default: ;
                endcase
            end
            MUL_VMACC: accumulator2_d = accumulator1_q;
            default: ;
        endcase
    end

    logic ex2_vsew_8, ex2_vsew_16, ex2_vsew_32;
    always_comb begin
        ex2_vsew_8  = DONT_CARE_ZERO ? '0 : 'x;
        ex2_vsew_16 = DONT_CARE_ZERO ? '0 : 'x;
        ex2_vsew_32 = DONT_CARE_ZERO ? '0 : 'x;
        unique case (state_ex2_q.eew)
            VSEW_8:  ex2_vsew_8 = 1'b1;
            VSEW_16: ex2_vsew_8 = 1'b0;
            VSEW_32: ex2_vsew_8 = 1'b0;
            default: ;
        endcase
        unique case (state_ex2_q.eew)
            VSEW_8:  ex2_vsew_16 = 1'b0;
            VSEW_16: ex2_vsew_16 = 1'b1;
            VSEW_32: ex2_vsew_16 = 1'b0;
            default: ;
        endcase
        unique case (state_ex2_q.eew)
            VSEW_8:  ex2_vsew_32 = 1'b0;
            VSEW_16: ex2_vsew_32 = 1'b0;
            VSEW_32: ex2_vsew_32 = 1'b1;
            default: ;
        endcase
    end

    // rearrange accumulator
    logic [MUL_OP_W*2-1:0] mul_acc;
    always_comb begin
        mul_acc = DONT_CARE_ZERO ? '0 : 'x;
        for (int i = 0; i < MUL_OP_W / 32; i++) begin
            mul_acc[64*i +: 64] = {
                // upper halfword for VSEW_32, byte 3 for VSEW_8
                ex2_vsew_8  ? 8'b0  : accumulator2_q[32*i+24 +: 8], ~ex2_vsew_32 ? accumulator2_q[32*i+24 +: 8] : accumulator2_q[32*i+16 +: 8],
                // upper halfword for VSEW_16, byte 2 for VSEW_8
                ex2_vsew_16 ? accumulator2_q[32*i+24 +: 8] : 8'b0, ex2_vsew_32 ? 8'b0 : accumulator2_q[32*i+16 +: 8],
                // byte 1 for VSEW_8
                ex2_vsew_32 ? 16'b0 : {8'b0, accumulator2_q[32*i+8  +: 8]},
                // lower halfword, byte 0 for VSEW_8
                ex2_vsew_8  ? 8'b0  : accumulator2_q[32*i+8 +: 8], accumulator2_q[32*i +: 8]
            };
        end
    end

    // accumulator flags
    logic mul_accflag, mul_accsub, mul_round;
    always_comb begin
        mul_accflag = DONT_CARE_ZERO ? '0 : 'x;
        unique case (state_ex2_q.mode.op)
            MUL_VMUL:  mul_accflag = 1'b0;
            MUL_VMULH: mul_accflag = 1'b0;
            MUL_VSMUL: mul_accflag = 1'b1;
            MUL_VMACC: mul_accflag = 1'b1;
            default: ;
        endcase
    end
    assign mul_accsub = state_ex2_q.mode.accsub;

    // perform signed multiplication of 17-bit integers and add 16-bit accumulator values
    logic [(MUL_OP_W/8)*33-1:0] mul_res;
    genvar g;
    generate
        for (g = 0; g < MUL_OP_W / 8; g++) begin
            vproc_mul_block #(
                .MUL_TYPE     ( MUL_TYPE                ),
                .BUF_OPS      ( BUF_MUL_IN              ),
                .BUF_MUL      ( BUF_MUL_OUT             ),
                .BUF_RES      ( 1'b0                    )
            ) mul_block (
                .clk_i        ( clk_i                   ),
                .async_rst_ni ( async_rst_ni            ),
                .sync_rst_ni  ( sync_rst_ni             ),
                .op1_i        ( mul_op1    [17*g +: 17] ),
                .op2_i        ( mul_op2    [17*g +: 17] ),
                .acc_i        ( mul_acc    [16*g +: 16] ),
                .acc_flag_i   ( mul_accflag             ),
                .acc_sub_i    ( mul_accsub              ),
                .res_o        ( mul_res    [33*g +: 33] )
            );
        end
    endgenerate

    // result for 32-bit mode
    logic [MUL_OP_W*2-1:0] res32;
    always_comb begin
        for (int i = 0; i < MUL_OP_W / 32; i++) begin
            res32[64*i +: 64] = { 32'b0                  , mul_res[132*i    +: 32]       } +
                                {{16{mul_res[132*i+65 ]}}, mul_res[132*i+33 +: 32], 16'b0} +
                                {{16{mul_res[132*i+131]}}, mul_res[132*i+99 +: 32], 16'b0} +
                                {                          mul_res[132*i+66 +: 32], 32'b0};
        end
    end

    // compose result
    always_comb begin
        result_d = DONT_CARE_ZERO ? '0 : 'x;
        unique case (state_ex3_q.mode.op)

            // multiplication retaining low part
            MUL_VMUL,
            MUL_VMACC: begin
                unique case (state_ex3_q.eew)
                    VSEW_8: begin
                        for (int i = 0; i < (MUL_OP_W / 8 ); i++)
                            result_d[8 *i +: 8 ] = mul_res[33*i +: 8 ];
                    end
                    VSEW_16: begin
                        for (int i = 0; i < (MUL_OP_W / 16); i++)
                            result_d[16*i +: 16] = mul_res[66*i +: 16];
                    end
                    VSEW_32: begin
                        for (int i = 0; i < (MUL_OP_W / 32); i++)
                            result_d[32*i +: 32] = res32  [64*i +: 32];
                    end
                    default: ;
                endcase
            end

            // multiplication retaining high part
            MUL_VMULH: begin
                unique case (state_ex3_q.eew)
                    VSEW_8: begin
                        for (int i = 0; i < (MUL_OP_W / 8 ); i++)
                            result_d[8 *i +: 8 ] = mul_res[33*i+8  +: 8 ];
                    end
                    VSEW_16: begin
                        for (int i = 0; i < (MUL_OP_W / 16); i++)
                            result_d[16*i +: 16] = mul_res[66*i+16 +: 16];
                    end
                    VSEW_32: begin
                        for (int i = 0; i < (MUL_OP_W / 32); i++)
                            result_d[32*i +: 32] = res32  [64*i+32 +: 32];
                    end
                    default: ;
                endcase
            end

            // multiplication with rounding and saturation
            MUL_VSMUL: begin
                unique case (state_ex3_q.eew)
                    VSEW_8: begin
                        for (int i = 0; i < (MUL_OP_W / 8 ); i++)
                            result_d[8 *i +: 8 ] = (mul_res[33*i+15] ^ mul_res[33*i+14]) ?  8'h7f       : mul_res[33*i+7  +: 8 ];
                    end
                    VSEW_16: begin
                        for (int i = 0; i < (MUL_OP_W / 16); i++)
                            result_d[16*i +: 16] = (mul_res[66*i+31] ^ mul_res[66*i+30]) ? 16'h7fff     : mul_res[66*i+15 +: 16];
                    end
                    VSEW_32: begin
                        for (int i = 0; i < (MUL_OP_W / 32); i++)
                            result_d[32*i +: 32] = (res32  [64*i+63] ^ res32  [64*i+62]) ? 32'h7fffffff : res32  [64*i+31 +: 32];
                    end
                    default: ;
                endcase
            end

            default: ;

        endcase
    end


`ifdef VPROC_SVA
`include "vproc_mul_sva.svh"
`endif

endmodule
