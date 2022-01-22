// Copyright TU Wien
// Licensed under the ISC license, see LICENSE.txt for details
// SPDX-License-Identifier: ISC


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
        input  vproc_pkg::cfg_lmul    lmul_i,
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
        logic                v0msk_shift;
        logic [4:0]          vs3;
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
            state_d.emul        = DONT_CARE_ZERO ? cfg_emul'('0) : cfg_emul'('x);
            if (~widening_i) begin
                state_d.eew = vsew_i;
                unique case (lmul_i)
                    LMUL_F8,
                    LMUL_F4,
                    LMUL_F2,
                    LMUL_1: state_d.emul = EMUL_1;
                    LMUL_2: state_d.emul = EMUL_2;
                    LMUL_4: state_d.emul = EMUL_4;
                    LMUL_8: state_d.emul = EMUL_8;
                    default: ;
                endcase
                state_d.vl = vl_i;
            end else begin
                state_d.eew = (vsew_i == VSEW_8) ? VSEW_16 : VSEW_32;
                unique case (lmul_i)
                    LMUL_F8,
                    LMUL_F4,
                    LMUL_F2: state_d.emul = EMUL_1;
                    LMUL_1:  state_d.emul = EMUL_2;
                    LMUL_2:  state_d.emul = EMUL_4;
                    LMUL_4:  state_d.emul = EMUL_8;
                    default: ;
                endcase
                state_d.vl = {vl_i[CFG_VL_W-2:0], 1'b1};
            end
            state_d.vl_0       = vl_0_i;
            state_d.rs1        = rs1_i;
            state_d.vs1_narrow = widening_i;
            state_d.vs1_fetch  = rs1_i.vreg;
            state_d.vs1_shift  = 1'b1;
            state_d.rs2        = rs2_i;
            if (mode_i.op2_is_vd) begin
                state_d.rs2.r.vaddr = vd_i;
            end
            state_d.vs2_narrow = widening_i;
            state_d.vs2_fetch  = 1'b1;
            state_d.vs2_shift  = 1'b1;
            state_d.v0msk_shift = 1'b1;
            state_d.vs3        = mode_i.op2_is_vd ? rs2_i.r.vaddr : vd_i;
            state_d.vs3_fetch  = mode_i.op == MUL_VMACC;
            state_d.vd         = vd_i;
            state_d.vd_store   = 1'b0;
            vreg_pend_wr_d     = vreg_pend_wr_i;
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
                state_d.vs3[2:0]  = state_q.vs3[2:0] + 3'b1;
                state_d.vs3_fetch = state_q.mode.op == MUL_VMACC;
                state_d.vd[2:0]   = state_q.vd[2:0] + 3'b1;
            end
            state_d.vs1_shift = ~state_q.vs1_narrow | state_q.count.part.low[0];
            state_d.vs2_shift = ~state_q.vs2_narrow | state_q.count.part.low[0];
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
    logic                       state_vreg_ready,   state_vs1_ready,   state_vs2_ready,   state_ex1_ready,   state_ex2_ready,   state_ex3_ready,   state_res_ready,   state_vd_ready;
    logic     state_init_stall,                                                                                                                                       state_vd_stall;
    logic     state_init_valid, state_vreg_valid_q, state_vs1_valid_q, state_vs2_valid_q, state_ex1_valid_q, state_ex2_valid_q, state_ex3_valid_q, state_res_valid_q, state_vd_valid_q;
    mul_state state_init,       state_vreg_q,       state_vs1_q,       state_vs2_q,       state_ex1_q,       state_ex2_q,       state_ex3_q,       state_res_q,       state_vd_q;
    always_comb begin
        state_init_valid      = state_valid_q;
        state_init            = state_q;
        state_init.last_cycle = state_valid_q & last_cycle;
        state_init.vd_store   = state_q.count.part.low == '1;
    end
    assign pipeline_ready = state_vreg_ready & ~state_init_stall;

    // common vreg read register:
    logic [VREG_W-1:0] vreg_rd_q, vreg_rd_d;

    // operand shift registers:
    logic [VREG_W-1:0] vs1_shift_q,   vs1_shift_d;
    logic [VREG_W-1:0] vs2_shift_q,   vs2_shift_d;
    logic [VREG_W-1:0] vs3_shift_q,   vs3_shift_d;
    logic [VREG_W-1:0] v0msk_shift_q, v0msk_shift_d;

    // temporary buffer for vs1 while fetching vs2:
    logic [MUL_OP_W-1:0] vs1_tmp_q, vs1_tmp_d;

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

    // result shift register:
    logic [VREG_W-1:0] vd_shift_q,    vd_shift_d;
    logic [VMSK_W-1:0] vdmsk_shift_q, vdmsk_shift_d;

    // vreg write buffers
    localparam WRITE_BUFFER_SZ = (MAX_WR_DELAY > 0) ? MAX_WR_DELAY : 1;
    logic              vreg_wr_en_q  [WRITE_BUFFER_SZ], vreg_wr_en_d;
    logic [4:0]        vreg_wr_addr_q[WRITE_BUFFER_SZ], vreg_wr_addr_d;
    logic [VMSK_W-1:0] vreg_wr_mask_q[WRITE_BUFFER_SZ], vreg_wr_mask_d;
    logic [VREG_W-1:0] vreg_wr_q     [WRITE_BUFFER_SZ], vreg_wr_d;

    // hazard clear registers
    logic [31:0] clear_wr_hazards_q, clear_wr_hazards_d;

    generate
        if (BUF_VREG) begin
            always_ff @(posedge clk_i or negedge async_rst_ni) begin : vproc_mul_stage_vreg_valid
                if (~async_rst_ni) begin
                    state_vreg_valid_q <= 1'b0;
                end
                else if (~sync_rst_ni) begin
                    state_vreg_valid_q <= 1'b0;
                end
                else if (state_vreg_ready) begin
                    state_vreg_valid_q <= state_init_valid & ~state_init_stall;
                end
            end
            always_ff @(posedge clk_i) begin : vproc_mul_stage_vreg
                // Note: state_init_valid is omitted here since vreg buffering
                // may need to proceed for one extra cycle after the
                // instruction has left state_init
                if (state_vreg_ready) begin
                    state_vreg_q <= state_init;
                    vreg_rd_q    <= vreg_rd_d;
                end
            end
            assign state_vreg_ready = ~state_vreg_valid_q | state_vs1_ready;
        end else begin
            always_comb begin
                state_vreg_valid_q = state_init_valid & ~state_init_stall;
                state_vreg_q       = state_init;
                vreg_rd_q          = vreg_rd_d;
            end
            assign state_vreg_ready = state_vs1_ready;
        end

        always_ff @(posedge clk_i or negedge async_rst_ni) begin : vproc_mul_stage_vs1_valid
            if (~async_rst_ni) begin
                state_vs1_valid_q <= 1'b0;
            end
            else if (~sync_rst_ni) begin
                state_vs1_valid_q <= 1'b0;
            end
            else if (state_vs1_ready) begin
                state_vs1_valid_q <= state_vreg_valid_q;
            end
        end
        always_ff @(posedge clk_i) begin : vproc_mul_stage_vs1
            if (state_vs1_ready & state_vreg_valid_q) begin
                state_vs1_q <= state_vreg_q;
                vs1_shift_q <= vs1_shift_d;
            end
        end
        assign state_vs1_ready = ~state_vs1_valid_q | state_vs2_ready;

        always_ff @(posedge clk_i or negedge async_rst_ni) begin : vproc_mul_stage_vs2_valid
            if (~async_rst_ni) begin
                state_vs2_valid_q <= 1'b0;
            end
            else if (~sync_rst_ni) begin
                state_vs2_valid_q <= 1'b0;
            end
            else if (state_vs2_ready) begin
                state_vs2_valid_q <= state_vs1_valid_q;
            end
        end
        always_ff @(posedge clk_i) begin : vproc_mul_stage_vs2
            if (state_vs2_ready & state_vs1_valid_q) begin
                state_vs2_q   <= state_vs1_q;
                vs2_shift_q   <= vs2_shift_d;
                vs3_shift_q   <= vs3_shift_d;
                v0msk_shift_q <= v0msk_shift_d;
                vs1_tmp_q     <= vs1_tmp_d;
            end
        end
        assign state_vs2_ready = ~state_vs2_valid_q | state_ex1_ready;

        if (BUF_OPERANDS) begin
            always_ff @(posedge clk_i or negedge async_rst_ni) begin : vproc_mul_stage_ex1_valid
                if (~async_rst_ni) begin
                    state_ex1_valid_q <= 1'b0;
                end
                else if (~sync_rst_ni) begin
                    state_ex1_valid_q <= 1'b0;
                end
                else if (state_ex1_ready) begin
                    state_ex1_valid_q <= state_vs2_valid_q;
                end
            end
            always_ff @(posedge clk_i) begin : vproc_mul_stage_ex1
                if (state_ex1_ready & state_vs2_valid_q) begin
                    state_ex1_q    <= state_vs2_q;
                    operand1_q     <= operand1_d;
                    operand2_q     <= operand2_d;
                    operand_mask_q <= operand_mask_d;
                    accumulator1_q <= accumulator1_d;
                end
            end
            assign state_ex1_ready = ~state_ex1_valid_q | state_ex2_ready;
        end else begin
            always_comb begin
                state_ex1_valid_q = state_vs2_valid_q;
                state_ex1_q       = state_vs2_q;
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

        always_ff @(posedge clk_i or negedge async_rst_ni) begin : vproc_mul_stage_vd_valid
            if (~async_rst_ni) begin
                state_vd_valid_q <= 1'b0;
            end
            else if (~sync_rst_ni) begin
                state_vd_valid_q <= 1'b0;
            end
            else if (state_vd_ready) begin
                state_vd_valid_q <= state_res_valid_q;
            end
        end
        always_ff @(posedge clk_i) begin : vproc_mul_stage_vd
            if (state_vd_ready & state_res_valid_q) begin
                state_vd_q    <= state_res_q;
                vd_shift_q    <= vd_shift_d;
                vdmsk_shift_q <= vdmsk_shift_d;
            end
        end
        assign state_vd_ready = ~state_vd_valid_q | ~state_vd_stall;

        if (MAX_WR_DELAY > 0) begin
            always_ff @(posedge clk_i) begin : vproc_mul_wr_delay
                vreg_wr_en_q  [0] <= vreg_wr_en_d;
                vreg_wr_addr_q[0] <= vreg_wr_addr_d;
                vreg_wr_mask_q[0] <= vreg_wr_mask_d;
                vreg_wr_q     [0] <= vreg_wr_d;
                for (int i = 1; i < MAX_WR_DELAY; i++) begin
                    vreg_wr_en_q  [i] <= vreg_wr_en_q  [i-1];
                    vreg_wr_addr_q[i] <= vreg_wr_addr_q[i-1];
                    vreg_wr_mask_q[i] <= vreg_wr_mask_q[i-1];
                    vreg_wr_q     [i] <= vreg_wr_q     [i-1];
                end
            end
        end

        always_ff @(posedge clk_i) begin
            clear_wr_hazards_q <= clear_wr_hazards_d;
        end
    endgenerate

    always_comb begin
        vreg_wr_en_o   = vreg_wr_en_d;
        vreg_wr_addr_o = vreg_wr_addr_d;
        vreg_wr_mask_o = vreg_wr_mask_d;
        vreg_wr_o      = vreg_wr_d;
        for (int i = 0; i < MAX_WR_DELAY; i++) begin
            if ((((i + 1) & (i + 2)) == 0) & vreg_wr_en_q[i]) begin
                vreg_wr_en_o   = 1'b1;
                vreg_wr_addr_o = vreg_wr_addr_q[i];
                vreg_wr_mask_o = vreg_wr_mask_q[i];
                vreg_wr_o      = vreg_wr_q     [i];
            end
        end
    end

    // write hazard clearing
    always_comb begin
        clear_wr_hazards_d     = vreg_wr_en_d                 ? (32'b1 << vreg_wr_addr_d                ) : 32'b0;
        if (MAX_WR_DELAY > 0) begin
            clear_wr_hazards_d = vreg_wr_en_q[MAX_WR_DELAY-1] ? (32'b1 << vreg_wr_addr_q[MAX_WR_DELAY-1]) : 32'b0;
        end
    end
    assign clear_wr_hazards_o = clear_wr_hazards_q;

    // Stall vreg reads until pending writes are complete; note that vreg read
    // stalling always happens in the init stage, since otherwise a substantial
    // amount of state would have to be forwarded (such as vreg_pend_wr_q)
    assign state_init_stall = (state_init.vs1_fetch   & vreg_pend_wr_q[state_init.rs1.r.vaddr]) |
                              (state_init.vs2_fetch   & vreg_pend_wr_q[state_init.rs2.r.vaddr]) |
                              (state_init.vs3_fetch   & vreg_pend_wr_q[state_init.vs3        ]) |
                              (state_init.first_cycle & state_init.mode.masked & vreg_pend_wr_q[0]);

    // Stall vreg writes until pending reads of the destination register are
    // complete and while the instruction is speculative
    assign state_vd_stall = state_vd_q.vd_store & (vreg_pend_rd_i[state_vd_q.vd] | instr_spec_i[state_vd_q.id]);

    assign instr_done_valid_o = state_vd_valid_q & state_vd_q.last_cycle & ~state_vd_stall;
    assign instr_done_id_o    = state_vd_q.id;

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
            EMUL_1: pend_vs3 = {31'b0, state_init.vs3_fetch} << state_init.vs3;
            EMUL_2: pend_vs3 = (32'h03 & ((32'h02 | {31'b0, state_init.vs3_fetch}) << state_init.count.part.mul[2:0])) << {state_init.vs3[4:1], 1'b0};
            EMUL_4: pend_vs3 = (32'h0F & ((32'h0E | {31'b0, state_init.vs3_fetch}) << state_init.count.part.mul[2:0])) << {state_init.vs3[4:2], 2'b0};
            EMUL_8: pend_vs3 = (32'hFF & ((32'hFE | {31'b0, state_init.vs3_fetch}) << state_init.count.part.mul[2:0])) << {state_init.vs3[4:3], 3'b0};
            default: ;
        endcase
    end
    // Note: vs2 is read in the second cycle; vs3 and the v0 mask have no extra
    // buffer and are always read in state_vs1
    assign vreg_pend_rd_o = ((
            ((state_init_valid & state_init.rs1.vreg              ) ? pend_vs1                        : '0) |
            ((state_init_valid                                    ) ? pend_vs2                        : '0) |
            ((state_init_valid & (state_init.mode.op == MUL_VMACC)) ? pend_vs3                        : '0) |
            ((state_init_valid & state_init.first_cycle           ) ? {31'b0, state_init.mode.masked} : '0)
        ) & ~vreg_pend_wr_q) |
    ((            state_vreg_valid_q & state_vreg_q.vs2_fetch  ) ? (32'h1 << state_vreg_q.rs2.r.vaddr) : '0) |
    ((~BUF_VREG & state_vs1_valid_q  & state_vs1_q.vs2_fetch   ) ? (32'h1 << state_vs1_q.rs2.r.vaddr ) : '0) |
    ((            state_vreg_valid_q & state_vreg_q.vs3_fetch  ) ? (32'h1 << state_vreg_q.vs3)         : '0) |
    ((            state_vs1_valid_q  & state_vs1_q.vs3_fetch   ) ? (32'h1 << state_vs1_q.vs3 )         : '0) |
    ((            state_vreg_valid_q & state_vreg_q.first_cycle) ? {31'b0, state_vreg_q.mode.masked}   : '0) |
    ((            state_vs1_valid_q  & state_vs1_q.first_cycle ) ? {31'b0, state_vs1_q.mode.masked}    : '0);


    ///////////////////////////////////////////////////////////////////////////
    // MUL REGISTER READ/WRITE:

    // source register addressing and read:
    assign vreg_rd_addr_o = (state_init.count.part.low[0] == 1'b0) ? state_init.rs1.r.vaddr : state_init.rs2.r.vaddr;
    assign vreg_rd_d      = vreg_rd_i;

    assign vreg_rd3_addr_o = state_vs1_q.vs3;

    // operand shift registers assignment:
    fetch_info vs1_info, vs2_info, v0msk_info;
    always_comb begin
        vs1_info.shift  = state_vreg_q.vs1_shift;
        vs1_info.fetch  = state_vreg_q.vs1_fetch;
        vs2_info.shift  = state_vs1_q.vs2_shift;
        vs2_info.fetch  = state_vs1_q.vs2_fetch;
        v0msk_info.shift = state_vs1_q.v0msk_shift;
        v0msk_info.fetch = state_vs1_q.first_cycle;
    end
    `VREGSHIFT_OPERAND_NARROW(VREG_W, MUL_OP_W, vs1_info, vreg_rd_q, vs1_shift_q, vs1_shift_d)
    `VREGSHIFT_OPERAND_NARROW(VREG_W, MUL_OP_W, vs2_info, vreg_rd_q, vs2_shift_q, vs2_shift_d)
    `VREGSHIFT_OPMASK(VREG_W, MUL_OP_W, v0msk_info, state_vs1_q.eew, vreg_mask_i, v0msk_shift_q, v0msk_shift_d)
    always_comb begin
        vs3_shift_d   = vreg_rd3_i;
        if (~state_vs1_q.vs3_fetch) begin
            vs3_shift_d[VREG_W-MUL_OP_W-1:0] = vs3_shift_q[VREG_W-1:MUL_OP_W];
        end
    end
    assign vs1_tmp_d = vs1_shift_q[MUL_OP_W-1:0];

    // conversion from source registers to operands:
    vproc_vregunpack #(
        .OP_W           ( MUL_OP_W                      ),
        .DONT_CARE_ZERO ( DONT_CARE_ZERO                )
    ) mul_vregunpack (
        .vsew_i         ( state_vs2_q.eew               ),
        .rs1_i          ( state_vs2_q.rs1               ),
        .vs1_i          ( vs1_tmp_q                     ),
        .vs1_narrow_i   ( state_vs2_q.vs1_narrow        ),
        .vs1_sigext_i   ( state_vs2_q.mode.op1_signed   ),
        .vs2_i          ( vs2_shift_q[MUL_OP_W-1:0]     ),
        .vs2_narrow_i   ( state_vs2_q.vs2_narrow        ),
        .vs2_sigext_i   ( state_vs2_q.mode.op2_signed   ),
        .vmsk_i         ( v0msk_shift_q[MUL_OP_W/8-1:0] ),
        .operand1_o     ( operand1_d                    ),
        .operand2_o     ( operand2_d                    ),
        .operand_mask_o ( operand_mask_d                )
    );
    assign accumulator1_d = vs3_shift_q[MUL_OP_W-1:0];

    // result byte mask:
    logic [VREG_W-1:0] vl_mask;
    assign vl_mask        = state_ex1_q.vl_0 ? {VREG_W{1'b0}} : ({VREG_W{1'b1}} >> (~state_ex1_q.vl));
    assign result_mask1_d = (state_ex1_q.mode.masked ? operand_mask_q : {(MUL_OP_W/8){1'b1}}) & vl_mask[state_ex1_q.count.val*MUL_OP_W/8 +: MUL_OP_W/8];

    assign result_mask2_d = result_mask1_q;
    assign result_mask3_d = result_mask2_q;

    // result shift register assignment:
    assign vd_shift_d    = {result_q      , vd_shift_q   [VREG_W-1:MUL_OP_W  ]};
    assign vdmsk_shift_d = {result_mask3_q, vdmsk_shift_q[VMSK_W-1:MUL_OP_W/8]};

    //
    assign vreg_wr_en_d   = state_vd_valid_q & state_vd_q.vd_store & ~state_vd_stall & ~instr_killed_i[state_vd_q.id];
    assign vreg_wr_addr_d = state_vd_q.vd;
    assign vreg_wr_mask_d = vreg_wr_en_o ? vdmsk_shift_q : '0;
    assign vreg_wr_d      = vd_shift_q;


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
    assign mul_round  = (state_ex2_q.mode.rounding == VXRM_RNU) | (state_ex2_q.mode.rounding == VXRM_RNE);

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
