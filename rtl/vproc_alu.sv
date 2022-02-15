// Copyright TU Wien
// Licensed under the Solderpad Hardware License v2.1, see LICENSE.txt for details
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1


module vproc_alu #(
        parameter int unsigned          VREG_W           = 128,  // width in bits of vector registers
        parameter int unsigned          VMSK_W           = 16,   // width of vector register masks (= VREG_W / 8)
        parameter int unsigned          CFG_VL_W         = 7,    // width of VL reg in bits (= log2(VREG_W))
        parameter int unsigned          ALU_OP_W         = 64,   // ALU operand width in bits
        parameter int unsigned          XIF_ID_W         = 3,    // width in bits of instruction IDs
        parameter int unsigned          XIF_ID_CNT       = 8,    // total count of instruction IDs
        parameter int unsigned          MAX_WR_ATTEMPTS  = 1,    // max required vregfile write attempts
        parameter bit                   BUF_VREG         = 1'b1, // insert pipeline stage after vreg read
        parameter bit                   BUF_OPERANDS     = 1'b1, // insert pipeline stage after operand extraction
        parameter bit                   BUF_INTERMEDIATE = 1'b1, // insert pipeline stage for intermediate results
        parameter bit                   BUF_RESULTS      = 1'b1, // insert pipeline stage after computing result
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

        input  vproc_pkg::op_mode_alu   mode_i,
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
        output logic [VREG_W-1:0]       vreg_wr_o,
        output logic [4:0]              vreg_wr_addr_o,
        output logic [VMSK_W-1:0]       vreg_wr_mask_o,
        output logic                    vreg_wr_en_o
    );

    import vproc_pkg::*;

    if ((ALU_OP_W & (ALU_OP_W - 1)) != 0 || ALU_OP_W < 32 || ALU_OP_W >= VREG_W) begin
        $fatal(1, "The vector ALU operand width ALU_OP_W must be at least 32, less than ",
                  "the vector register width VREG_W and a power of two.  ",
                  "The current value of %d is invalid.", ALU_OP_W);
    end

    if (MAX_WR_ATTEMPTS < 1 || (1 << (MAX_WR_ATTEMPTS - 1)) > VREG_W / ALU_OP_W) begin
        $fatal(1, "The maximum number of write attempts MAX_WR_ATTEMPTS of a unit ",
                  "must be at least 1 and 2^(MAX_WR_ATTEMPTS-1) must be less than or ",
                  "equal to the ratio of the vector register width vs the operand width ",
                  "of that unit.  ",
                  "For the vector ALU MAX_WR_ATTEMPTS is %d and that ratio is %d.",
                  MAX_WR_ATTEMPTS, VREG_W / ALU_OP_W);
    end

    // max number of cycles by which a write can be delayed
    localparam int unsigned MAX_WR_DELAY = (1 << (MAX_WR_ATTEMPTS - 1)) - 1;


    ///////////////////////////////////////////////////////////////////////////
    // ALU STATE:

    localparam int unsigned ALU_CYCLES_PER_VREG = VREG_W / ALU_OP_W;
    localparam int unsigned ALU_COUNTER_W       = $clog2(ALU_CYCLES_PER_VREG) + 3;

    typedef union packed {
        logic [ALU_COUNTER_W-1:0] val;
        struct packed {
            logic [2:0]               mul; // mul part (vreg index)
            logic [ALU_COUNTER_W-4:0] low; // counter part in vreg (vreg pos)
        } part;
    } alu_counter;

    typedef struct packed {
        alu_counter          count;
        logic                first_cycle;
        logic                last_cycle;
        logic [XIF_ID_W-1:0] id;
        op_mode_alu          mode;
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
        logic [4:0]          vd;
        logic                vd_narrow;
        logic                vd_store;
    } alu_state;

    logic        state_valid_q,  state_valid_d;
    alu_state    state_q,        state_d;
    logic [31:0] vreg_pend_wr_q, vreg_pend_wr_d; // local copy of global vreg write mask
    always_ff @(posedge clk_i or negedge async_rst_ni) begin : vproc_alu_state_valid
        if (~async_rst_ni) begin
            state_valid_q <= 1'b0;
        end
        else if (~sync_rst_ni) begin
            state_valid_q <= 1'b0;
        end else begin
            state_valid_q <= state_valid_d;
        end
    end
    always_ff @(posedge clk_i) begin : vproc_alu_state
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
            state_d.vs2_fetch   = rs2_i.vreg;
            state_d.vs2_shift   = 1'b1;
            state_d.v0msk_fetch = 1'b1;
            state_d.v0msk_shift = 1'b1;
            state_d.vd          = vd_i;
            state_d.vd_narrow   = widenarrow_i == OP_NARROWING;
            state_d.vd_store    = 1'b0;
            vreg_pend_wr_d      = vreg_pend_wr_i;
        end
        else if (state_valid_q & pipeline_ready) begin
            state_d.count.val   = state_q.count.val + 1;
            state_valid_d       = ~last_cycle;
            state_d.first_cycle = 1'b0;
            state_d.vs1_fetch   = 1'b0;
            state_d.vs2_fetch   = 1'b0;
            if (state_q.count.part.low == '1) begin
                if (state_q.rs1.vreg & (~state_q.vs1_narrow | state_q.count.part.mul[0])) begin
                    state_d.rs1.r.vaddr[2:0] = state_q.rs1.r.vaddr[2:0] + 3'b1;
                    state_d.vs1_fetch        = state_q.rs1.vreg;
                end
                if (~state_q.vs2_narrow | state_q.count.part.mul[0]) begin
                    state_d.rs2.r.vaddr[2:0] = state_q.rs2.r.vaddr[2:0] + 3'b1;
                    state_d.vs2_fetch        = state_q.rs2.vreg;
                end
                if (~state_q.mode.cmp & (~state_q.vd_narrow | state_q.count.part.mul[0])) begin
                    state_d.vd[2:0] = state_q.vd[2:0] + 3'b1;
                end
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
    // ALU PIPELINE BUFFERS:

    // pass state information along pipeline:
    logic                        state_ex1_ready,                      state_ex2_ready,   state_res_ready,   state_vd_ready;
    logic     state_init_stall,                                                           state_vd_stall;
    logic     state_init_valid,  state_ex1_valid_q, state_ex1_valid_d, state_ex2_valid_q, state_res_valid_q;
    logic     state_init_masked;
    alu_state state_init,        state_ex1_q,       state_ex1_d,       state_ex2_q,       state_res_q;
    always_comb begin
        state_init_valid      = state_valid_q;
        state_init            = state_q;
        state_init.last_cycle = state_valid_q & last_cycle;
        state_init.vd_store   = (state_q.count.part.low == '1) & (~state_q.vd_narrow | state_q.count.part.mul[0]);
    end
    logic unpack_ready;
    assign pipeline_ready = unpack_ready & ~state_init_stall;

    // operands and result:
    logic [ALU_OP_W*9/8-1:0] operand1_q,     operand1_d;
    logic [ALU_OP_W*9/8-1:0] operand2_q,     operand2_d;
    logic [ALU_OP_W  /8-1:0] operand_mask_q, operand_mask_d;
    logic [ALU_OP_W    -1:0] result_alu_q,   result_alu_d;
    logic [ALU_OP_W  /8-1:0] result_cmp_q,   result_cmp_d;
    logic [ALU_OP_W  /8-1:0] result_mask_q,  result_mask_d;

    // intermediate results:
    logic [ALU_OP_W    -1:0] operand1_tmp_q,     operand1_tmp_d;
    logic [ALU_OP_W    -1:0] operand2_tmp_q,     operand2_tmp_d;
    logic [ALU_OP_W  /8-1:0] operand_mask_tmp_q, operand_mask_tmp_d;
    logic [ALU_OP_W*9/8-1:0] sum_q,              sum_d;
    logic [ALU_OP_W  /8-1:0] cmp_q,              cmp_d;
    logic [ALU_OP_W  /4-1:0] satval_q,           satval_d;
    logic [ALU_OP_W    -1:0] shift_res_q,        shift_res_d;

    generate
        if (BUF_OPERANDS) begin
            always_ff @(posedge clk_i or negedge async_rst_ni) begin : vproc_alu_stage_ex1_valid
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
            always_ff @(posedge clk_i) begin : vproc_alu_stage_ex1
                if (state_ex1_ready & state_ex1_valid_d) begin
                    state_ex1_q    <= state_ex1_d;
                    operand1_q     <= operand1_d;
                    operand2_q     <= operand2_d;
                    operand_mask_q <= operand_mask_d;
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
            end
            assign state_ex1_ready = state_ex2_ready;
        end

        if (BUF_INTERMEDIATE) begin
            always_ff @(posedge clk_i or negedge async_rst_ni) begin : vproc_alu_stage_ex2_valid
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
            always_ff @(posedge clk_i) begin : vproc_alu_stage_ex2
                if (state_ex2_ready & state_ex1_valid_q) begin
                    state_ex2_q        <= state_ex1_q;
                    operand1_tmp_q     <= operand1_tmp_d;
                    operand2_tmp_q     <= operand2_tmp_d;
                    operand_mask_tmp_q <= operand_mask_tmp_d;
                    sum_q              <= sum_d;
                    cmp_q              <= cmp_d;
                    satval_q           <= satval_d;
                    shift_res_q        <= shift_res_d;
                end
            end
            assign state_ex2_ready = ~state_ex2_valid_q | state_res_ready;
        end else begin
            always_comb begin
                state_ex2_valid_q   = state_ex1_valid_q;
                state_ex2_q         = state_ex1_q;
                operand1_tmp_q      = operand1_tmp_d;
                operand2_tmp_q      = operand2_tmp_d;
                operand_mask_tmp_q  = operand_mask_tmp_d;
                sum_q               = sum_d;
                cmp_q               = cmp_d;
                satval_q            = satval_d;
                shift_res_q         = shift_res_d;
            end
            assign state_ex2_ready = state_res_ready;
        end

        if (BUF_RESULTS) begin
            always_ff @(posedge clk_i or negedge async_rst_ni) begin : vproc_alu_stage_res_valid
                if (~async_rst_ni) begin
                    state_res_valid_q <= 1'b0;
                end
                else if (~sync_rst_ni) begin
                    state_res_valid_q <= 1'b0;
                end
                else if (state_res_ready) begin
                    state_res_valid_q <= state_ex2_valid_q;
                end
            end
            always_ff @(posedge clk_i) begin : vproc_alu_stage_res
                if (state_res_ready & state_ex2_valid_q) begin
                    state_res_q   <= state_ex2_q;
                    result_alu_q  <= result_alu_d;
                    result_cmp_q  <= result_cmp_d;
                    result_mask_q <= result_mask_d;
                end
            end
            assign state_res_ready = ~state_res_valid_q | state_vd_ready;
        end else begin
            always_comb begin
                state_res_valid_q = state_ex2_valid_q;
                state_res_q       = state_ex2_q;
                result_alu_q      = result_alu_d;
                result_cmp_q      = result_cmp_d;
                result_mask_q     = result_mask_d;
            end
            assign state_res_ready = state_vd_ready;
        end
    endgenerate

    // Stall vreg reads until pending writes are complete; note that vreg read
    // stalling always happens in the init stage, since otherwise a substantial
    // amount of state would have to be forwarded (such as vreg_pend_wr_q)
    assign state_init_stall = (state_init.vs1_fetch   & vreg_pend_wr_q[state_init.rs1.r.vaddr]) |
                              (state_init.vs2_fetch   & vreg_pend_wr_q[state_init.rs2.r.vaddr]) |
                              (state_init.v0msk_fetch & state_init_masked & vreg_pend_wr_q[0]);

    // pending vreg reads
    // Note: The pipeline might stall while reading a vreg, hence a vreg has to
    // be part of the pending reads until the read is complete.
    logic [31:0] pend_vs1,  pend_vs2;
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
    end
    // Determine whether there is a pending read of v0 as a mask
    assign state_init_masked = state_init.mode.op_mask   != ALU_MASK_NONE;
    // Note: vs2 is read in the second cycle; the v0 mask has no extra buffer
    // and is always read in state_vs1
    logic [31:0] unpack_pend_rd;
    assign vreg_pend_rd_o = ((
            ((state_init_valid & state_init.rs1.vreg   ) ? pend_vs1                   : '0) |
            ((state_init_valid & state_init.rs2.vreg   ) ? pend_vs2                   : '0) |
            ((state_init_valid & state_init.v0msk_fetch) ? {31'b0, state_init_masked} : '0)
        ) & ~vreg_pend_wr_q) |
    unpack_pend_rd;


    ///////////////////////////////////////////////////////////////////////////
    // ALU REGISTER READ/WRITE AND CONVERSION

    unpack_flags [2:0]       unpack_op_flags;
    logic        [2:0][4 :0] unpack_op_vaddr;
    logic        [2:0][31:0] unpack_op_xval;
    always_comb begin
        unpack_op_flags  [0]          = unpack_flags'('0);
        unpack_op_flags  [0].shift    = state_init.vs1_shift;
        unpack_op_flags  [0].load     = state_init.vs1_fetch;
        unpack_op_flags  [0].vreg     = state_init.rs1.vreg;
        unpack_op_flags  [0].elemwise = '0;
        unpack_op_flags  [0].narrow   = state_init.vs1_narrow;
        unpack_op_flags  [0].sigext   = state_init.mode.sigext;
        unpack_op_vaddr  [0]          = state_init.rs1.r.vaddr;
        unpack_op_xval   [0]          = state_init.rs1.r.xval;
        unpack_op_flags  [1]          = unpack_flags'('0);
        unpack_op_flags  [1].shift    = state_init.vs2_shift;
        unpack_op_flags  [1].load     = state_init.vs2_fetch;
        unpack_op_flags  [1].elemwise = '0;
        unpack_op_flags  [1].narrow   = state_init.vs2_narrow;
        unpack_op_flags  [1].sigext   = state_init.mode.sigext;
        unpack_op_vaddr  [1]          = state_init.rs2.r.vaddr;
        unpack_op_xval   [1]          = '0;
        unpack_op_flags  [2]          = unpack_flags'('0);
        unpack_op_flags  [2].shift    = state_init.v0msk_shift;
        unpack_op_flags  [2].load     = state_init.v0msk_fetch & state_init_masked;
        unpack_op_flags  [2].elemwise = '0;
        unpack_op_vaddr  [2]          = '0;
        unpack_op_xval   [2]          = '0;
    end

    localparam int unsigned UNPACK_VPORT_W [2] = '{VREG_W,VREG_W};
    localparam int unsigned UNPACK_VADDR_W [2] = '{5,5};
    localparam int unsigned UNPACK_OP_W    [3] = '{ALU_OP_W,ALU_OP_W,ALU_OP_W/8};
    localparam int unsigned UNPACK_OP_STAGE[3] = '{1,2,2};
    localparam int unsigned UNPACK_OP_SRC  [3] = '{0,0,1};

    logic [2:0][ALU_OP_W-1:0] unpack_ops;
    logic [1:0][4:0]          unpack_vreg_addr;
    logic [1:0][VREG_W-1:0]   unpack_vreg_data;
    vproc_vregunpack #(
        .MAX_VPORT_W          ( VREG_W                               ),
        .MAX_VADDR_W          ( 5                                    ),
        .VPORT_CNT            ( 2                                    ),
        .VPORT_W              ( UNPACK_VPORT_W                       ),
        .VADDR_W              ( UNPACK_VADDR_W                       ),
        .VPORT_ADDR_ZERO      ( 2'b10                                ),
        .VPORT_BUFFER         ( 2'b01                                ),
        .MAX_OP_W             ( ALU_OP_W                             ),
        .OP_CNT               ( 3                                    ),
        .OP_W                 ( UNPACK_OP_W                          ),
        .OP_STAGE             ( UNPACK_OP_STAGE                      ),
        .OP_SRC               ( UNPACK_OP_SRC                        ),
        .OP_ADDR_OFFSET_OP0   ( 3'b000                               ),
        .OP_MASK              ( 3'b100                               ),
        .OP_XREG              ( 3'b001                               ),
        .OP_NARROW            ( 3'b011                               ),
        .OP_ALLOW_ELEMWISE    ( 3'b000                               ),
        .OP_ALWAYS_ELEMWISE   ( 3'b000                               ),
        .OP_HOLD_FLAG         ( 3'b000                               ),
        .UNPACK_STAGES        ( 3                                    ),
        .FLAGS_T              ( unpack_flags                         ),
        .CTRL_DATA_W          ( $bits(alu_state)                     ),
        .DONT_CARE_ZERO       ( DONT_CARE_ZERO                       )
    ) alu_unpack (
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
    assign vreg_rd_addr_o = unpack_vreg_addr[0];
    always_comb begin
        unpack_vreg_data[0] = vreg_rd_i;
        unpack_vreg_data[1] = vreg_mask_i;
    end
    logic [ALU_OP_W-1:0] operand1, operand2;
    assign operand1       = unpack_ops[0];
    assign operand2       = unpack_ops[1];
    assign operand_mask_d = unpack_ops[2][ALU_OP_W/8-1:0];

    logic [ALU_OP_W*9/8-1:0] operand1_9bpb;
    always_comb begin
        operand1_9bpb = DONT_CARE_ZERO ? '0 : 'x;
        for (int i = 0; i < ALU_OP_W / 8; i++) begin
            if (~state_ex1_d.mode.shift_op) begin
                operand1_9bpb[9*i+1 +: 8] = operand1[8*i +: 8];
            end else begin
                operand1_9bpb[9*i   +: 8] = operand1[8*i +: 8];
                unique case (state_ex1_d.eew)
                    VSEW_8: begin
                        operand1_9bpb[9*i+8] =                  state_ex1_d.mode.sigext & operand1[8*i+7];
                    end
                    VSEW_16: begin
                        operand1_9bpb[9*i+8] = ((i & 1) == 1) ? state_ex1_d.mode.sigext & operand1[8*i+7] : operand1[8*i+8];
                    end
                    VSEW_32: begin
                        operand1_9bpb[9*i+8] = ((i & 3) == 3) ? state_ex1_d.mode.sigext & operand1[8*i+7] : operand1[8*i+8];
                    end
                    default: ;
                endcase
            end
        end
    end
    logic [ALU_OP_W*9/8-1:0] operand2_9bpb;
    always_comb begin
        operand2_9bpb = DONT_CARE_ZERO ? '0 : 'x;
        for (int i = 0; i < ALU_OP_W / 8; i++) begin
            if (~state_ex1_d.mode.shift_op) begin
                operand2_9bpb[9*i+1 +: 8] = operand2[8*i +: 8];
            end else begin
                operand2_9bpb[9*i   +: 8] = operand2[8*i +: 8];
                unique case (state_ex1_d.eew)
                    VSEW_8: begin
                        operand2_9bpb[9*i+8] =                  state_ex1_d.mode.sigext & operand2[8*i+7];
                    end
                    VSEW_16: begin
                        operand2_9bpb[9*i+8] = ((i & 1) == 1) ? state_ex1_d.mode.sigext & operand2[8*i+7] : operand2[8*i+8];
                    end
                    VSEW_32: begin
                        operand2_9bpb[9*i+8] = ((i & 3) == 3) ? state_ex1_d.mode.sigext & operand2[8*i+7] : operand2[8*i+8];
                    end
                    default: ;
                endcase
            end
        end
    end

    logic [ALU_OP_W/8-1:0] carry_in_mask;
    always_comb begin
        carry_in_mask = '0;
        for (int i = 0; i < ALU_OP_W / 8; i++) begin
            if (state_ex1_d.mode.op_mask == ALU_MASK_CARRY) begin
                carry_in_mask[i] = operand_mask_d[i];
            end
            if (state_ex1_d.mode.shift_op) begin
                // Select carry in for averaging add/subtract rounding; the averaging add/subtract
                // instructions shift the result of the add/subtract right by one bit.  The result
                // is rounded based on its least significant bit as well as the bit that is shifted
                // out, depending on the rounding mode.  The carry in has the effect of rounding up
                // the result if the bit that is shifted out was set.
                unique case (state_ex1_d.vxrm)
                    // round-to-nearest-up: always carry in
                    VXRM_RNU: carry_in_mask[i] =  operand1_9bpb[9*i] | operand2_9bpb[9*i];
                    // round-to-nearest-even: carry in if the shifted result (w/o carry) would be odd
                    VXRM_RNE: carry_in_mask[i] = (operand1_9bpb[9*i] | operand2_9bpb[9*i]) & (operand1_9bpb[9*i+1] != operand2_9bpb[9*i+1]);
                    // round-down: no carry in
                    VXRM_RDN: carry_in_mask[i] =  operand1_9bpb[9*i] & operand2_9bpb[9*i];
                    // round-to-odd: carry in if the shifted result (w/o carry) would be even
                    VXRM_ROD: carry_in_mask[i] = (operand1_9bpb[9*i] | operand2_9bpb[9*i]) & (operand1_9bpb[9*i+1] == operand2_9bpb[9*i+1]);
                    default: ;
                endcase
            end
        end
    end
    logic state_vs2_subtract;
    assign state_vs2_subtract = state_ex1_d.mode.inv_op1 | state_ex1_d.mode.inv_op2;
    always_comb begin
        operand1_d = state_ex1_d.mode.inv_op1 ? ~operand1_9bpb : operand1_9bpb;
        operand2_d = state_ex1_d.mode.inv_op2 ? ~operand2_9bpb : operand2_9bpb;
        for (int i = 0; i < ALU_OP_W / 32; i++) begin
            // operands carry logic for fracturable adder
            operand1_d[36*i   ] =                                 carry_in_mask[i*4  ] ^ state_vs2_subtract;
            operand1_d[36*i+9 ] = (state_ex1_d.eew == VSEW_8 ) ? (carry_in_mask[i*4+1] ^ state_vs2_subtract) : 1'b1;
            operand1_d[36*i+18] = (state_ex1_d.eew != VSEW_32) ? (carry_in_mask[i*4+2] ^ state_vs2_subtract) : 1'b1;
            operand1_d[36*i+27] = (state_ex1_d.eew == VSEW_8 ) ? (carry_in_mask[i*4+3] ^ state_vs2_subtract) : 1'b1;
            operand2_d[36*i   ] = 1'b1;
            operand2_d[36*i+9 ] = (state_ex1_d.eew == VSEW_8 ) ? (carry_in_mask[i*4+1] ^ state_vs2_subtract) : 1'b0;
            operand2_d[36*i+18] = (state_ex1_d.eew != VSEW_32) ? (carry_in_mask[i*4+2] ^ state_vs2_subtract) : 1'b0;
            operand2_d[36*i+27] = (state_ex1_d.eew == VSEW_8 ) ? (carry_in_mask[i*4+3] ^ state_vs2_subtract) : 1'b0;
        end
    end

    logic [ALU_OP_W-1:0] operand1_32, operand2_32;
    always_comb begin
        for (int i = 0; i < ALU_OP_W / 32; i++) begin
            operand1_32[32*i +: 32] = {operand1_q[36*i+28 +: 8], operand1_q[36*i+19 +: 8], operand1_q[36*i+10 +: 8], operand1_q[36*i+1 +: 8]};
            operand2_32[32*i +: 32] = {operand2_q[36*i+28 +: 8], operand2_q[36*i+19 +: 8], operand2_q[36*i+10 +: 8], operand2_q[36*i+1 +: 8]};
        end
    end
    assign operand1_tmp_d     = operand1_32;
    assign operand2_tmp_d     = operand2_32;
    assign operand_mask_tmp_d = operand_mask_q;

    // result byte mask:
    logic [VREG_W-1:0] vl_mask;
    assign vl_mask       = state_ex2_q.vl_0 ? {VREG_W{1'b0}} : ({VREG_W{1'b1}} >> (~state_ex2_q.vl));
    assign result_mask_d = ((state_ex2_q.mode.op_mask == ALU_MASK_WRITE) ? operand_mask_tmp_q : {(ALU_OP_W/8){1'b1}}) & vl_mask[state_ex2_q.count.val*ALU_OP_W/8 +: ALU_OP_W/8];

    // The result is inverted for averaging subtract instructions (i.e., instructions for
    // which the operands are shifted right and at least one operand is being inverted).
    // This is required to allow using the carry logic for rounding.
    logic [ALU_OP_W-1:0] vd_alu_finalized;
    always_comb begin
        vd_alu_finalized = result_alu_q;
        if (state_res_q.mode.shift_op & (state_res_q.mode.inv_op1 | state_res_q.mode.inv_op2)) begin
            vd_alu_finalized = ~result_alu_q;
        end
    end

    logic      [1:0]               pack_res_store, pack_res_valid;
    pack_flags [1:0]               pack_res_flags;
    logic      [1:0][ALU_OP_W-1:0] pack_res_data, pack_res_mask;
    always_comb begin
        pack_res_data = '0;
        pack_res_mask = '0;

        pack_res_flags[0]                 = pack_flags'('0);
        pack_res_store[0]                 = state_res_q.vd_store & ~state_res_q.mode.cmp;
        pack_res_flags[0].shift           = ~state_res_q.vd_narrow | ~state_res_q.count.val[0];
        pack_res_flags[0].narrow          = state_res_q.vd_narrow;
        pack_res_flags[0].saturate        = state_res_q.mode.sat_res;
        pack_res_flags[0].sig             = state_res_q.mode.sigext;
        pack_res_valid[0]                 = state_res_valid_q;
        pack_res_data [0]                 = vd_alu_finalized;
        pack_res_mask [0][ALU_OP_W/8-1:0] = result_mask_q;

        pack_res_flags[1]                 = pack_flags'('0);
        pack_res_flags[1].mul_idx         = state_res_q.count.part.mul;
        pack_res_store[1]                 = state_res_q.vd_store & state_res_q.mode.cmp;
        pack_res_valid[1]                 = state_res_valid_q;
        pack_res_data [1][ALU_OP_W/8-1:0] = result_cmp_q;
        pack_res_mask [1][ALU_OP_W/8-1:0] = result_mask_q;
    end
    logic pack_pend_clear;
    assign pack_pend_clear = state_res_q.mode.cmp ? state_res_q.last_cycle : state_res_q.vd_store;
    localparam int unsigned PACK_RES_W[2] = '{ALU_OP_W, ALU_OP_W/8};
    vproc_vregpack #(
        .VPORT_W                     ( VREG_W                 ),
        .VADDR_W                     ( 5                      ),
        .VPORT_WR_ATTEMPTS           ( MAX_WR_ATTEMPTS        ),
        .VPORT_PEND_CLR_BULK         ( '0                     ),
        .MAX_RES_W                   ( ALU_OP_W               ),
        .RES_CNT                     ( 2                      ),
        .RES_W                       ( PACK_RES_W             ),
        .RES_MASK                    ( 2'b10                  ),
        .RES_XREG                    ( '0                     ),
        .RES_NARROW                  ( 2'b01                  ),
        .RES_ALLOW_ELEMWISE          ( '0                     ),
        .RES_ALWAYS_ELEMWISE         ( '0                     ),
        .FLAGS_T                     ( pack_flags             ),
        .INSTR_ID_W                  ( XIF_ID_W               ),
        .INSTR_ID_CNT                ( XIF_ID_CNT             ),
        .DONT_CARE_ZERO              ( DONT_CARE_ZERO         )
    ) alu_pack (
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
        .pipe_in_pend_clr_i          ( pack_pend_clear        ),
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
    // ALU ARITHMETIC:

    logic state_ex1_subtract;
    assign state_ex1_subtract = state_ex1_q.mode.inv_op1 | state_ex1_q.mode.inv_op2;

    // 37-bit adder (fracturable 32-bit adder with carry-in and carry-out)
    logic [ALU_OP_W*37/32-1:0] sum37;
    always_comb begin
        sum37 = DONT_CARE_ZERO ? '0 : 'x;
        for (int i = 0; i < ALU_OP_W / 32; i++) begin
            sum37[37*i +: 37] = {1'b0, operand2_q[36*i +: 36]} + {1'b0, operand1_q[36*i +: 36]};
        end
    end
    logic [ALU_OP_W/8-1:0] carry, sig_op1, sig_op2, sig_res;
    always_comb begin
        sum_d   = DONT_CARE_ZERO ? '0 : 'x;
        carry   = DONT_CARE_ZERO ? '0 : 'x;
        sig_op1 = DONT_CARE_ZERO ? '0 : 'x;
        sig_op2 = DONT_CARE_ZERO ? '0 : 'x;
        sig_res = DONT_CARE_ZERO ? '0 : 'x;
        for (int i = 0; i < ALU_OP_W / 32; i++) begin
            // discard lowest bit of the 37-bit result and fill in carry chain bits
            sum_d[36*i    +: 8] = sum37[37*i+1  +: 8];
            sum_d[36*i+9  +: 8] = sum37[37*i+10 +: 8];
            sum_d[36*i+18 +: 8] = sum37[37*i+19 +: 8];
            sum_d[36*i+27 +: 8] = sum37[37*i+28 +: 8];
            unique case (state_ex1_q.eew)
                VSEW_8: begin
                    sum_d  [36*i+8   ] =  sum37     [37*i+9 ] ^ state_ex1_subtract;
                    sum_d  [36*i+17  ] =  sum37     [37*i+18] ^ state_ex1_subtract;
                    sum_d  [36*i+26  ] =  sum37     [37*i+27] ^ state_ex1_subtract;
                    sum_d  [36*i+35  ] =  sum37     [37*i+36] ^ state_ex1_subtract;
                    carry  [4 *i +: 4] = {sum37     [37*i+36], sum37     [37*i+27], sum37     [37*i+18], sum37     [37*i+9]};
                    sig_op1[4 *i +: 4] = {operand1_q[36*i+35], operand1_q[36*i+26], operand1_q[36*i+17], operand1_q[36*i+8]};
                    sig_op2[4 *i +: 4] = {operand2_q[36*i+35], operand2_q[36*i+26], operand2_q[36*i+17], operand2_q[36*i+8]};
                    sig_res[4 *i +: 4] = {sum37     [37*i+35], sum37     [37*i+26], sum37     [37*i+17], sum37     [37*i+8]};
                end
                VSEW_16: begin
                    sum_d  [36*i+8   ] =     sum37     [37*i+10];
                    sum_d  [36*i+17  ] =     sum37     [37*i+18] ^ state_ex1_subtract;
                    sum_d  [36*i+26  ] =     sum37     [37*i+28];
                    sum_d  [36*i+35  ] =     sum37     [37*i+36] ^ state_ex1_subtract;
                    carry  [4 *i +: 4] = {{2{sum37     [37*i+36]}}, {2{sum37     [37*i+18]}}};
                    sig_op1[4 *i +: 4] = {{2{operand1_q[36*i+35]}}, {2{operand1_q[36*i+17]}}};
                    sig_op2[4 *i +: 4] = {{2{operand2_q[36*i+35]}}, {2{operand2_q[36*i+17]}}};
                    sig_res[4 *i +: 4] = {{2{sum37     [37*i+35]}}, {2{sum37     [37*i+17]}}};
                end
                VSEW_32: begin
                    sum_d  [36*i+8   ] =    sum37     [37*i+10];
                    sum_d  [36*i+17  ] =    sum37     [37*i+19];
                    sum_d  [36*i+26  ] =    sum37     [37*i+28];
                    sum_d  [36*i+35  ] =    sum37     [37*i+36] ^ state_ex1_subtract;
                    carry  [4 *i +: 4] = {4{sum37     [37*i+36]}};
                    sig_op1[4 *i +: 4] = {4{operand1_q[36*i+35]}};
                    sig_op2[4 *i +: 4] = {4{operand2_q[36*i+35]}};
                    sig_res[4 *i +: 4] = {4{sum37     [37*i+35]}};
                end
                default: ;
            endcase
        end
    end
    // signed arithmetic overflow flag (note that subtraction is implemented by
    // inverting the subtrahend and adding it with carry to the minuend; hence
    // the logic for detecting overflow always follows the rules for addition:
    // signed overflow occurs when the operands have equal sign and the sign of
    // the result is different)
    logic [ALU_OP_W/8-1:0] ovflw;
    assign ovflw = ~(sig_op1 ^ sig_op2) & (sig_op1 ^ sig_res);
    always_comb begin
        cmp_d = DONT_CARE_ZERO ? '0 : 'x;
        unique case (state_ex1_q.mode.opx1.sel)
            ALU_SEL_CARRY: cmp_d = state_ex1_subtract ? ~carry : carry;
            ALU_SEL_OVFLW: cmp_d = ovflw;
            ALU_SEL_LT:    cmp_d = ovflw ^ sig_res; // minuend is less than subtrahend
            ALU_SEL_MASK: begin
                for (int i = 0; i < ALU_OP_W / 8; i++) begin
                    unique case (state_ex1_q.mode.op_mask)
                        ALU_MASK_NONE: cmp_d[i] = 1'b0;
                        ALU_MASK_SEL:  cmp_d[i] = operand_mask_q[i];
                        default: ;
                    endcase
                end
            end
            default: ;
        endcase
    end
    // saturation value generation: generate the sign bit and fill bit for
    // saturation values of the result of the addition (used by saturating add
    // and subtract instructions); differentiation between signed and unsigned
    // mode is done based on whether the carry or the overflow bit is saved in
    // the compare register `cmp_q'; for signed overflow the sign bit of the
    // result is inverted, while the fill bit (i.e., all other bits of the
    // final result) is the initial sign of the result (hence the fill bit
    // is always different from the sign bit); for unsigned operations the
    // carry bit fills the entire final result (sign bit and fill bit equal)
    logic mode_signed;
    always_comb begin
        mode_signed = DONT_CARE_ZERO ? '0 : 'x;
        unique case (state_ex1_q.mode.opx1.sel)
            ALU_SEL_CARRY: mode_signed = 1'b0;
            ALU_SEL_OVFLW: mode_signed = 1'b1;
            default: ;
        endcase
    end
    always_comb begin
        satval_d = DONT_CARE_ZERO ? '0 : 'x;
        unique case (state_ex1_q.eew)
            VSEW_8: begin
                for (int i = 0; i < ALU_OP_W / 8 ; i++) begin
                    satval_d[2*i +: 2] = mode_signed ? {~sig_res[  i],    sig_res[  i]  } : {2{carry[  i]}};
                end
            end
            VSEW_16: begin
                for (int i = 0; i < ALU_OP_W / 16; i++) begin
                    satval_d[4*i +: 4] = mode_signed ? {~sig_res[2*i], {3{sig_res[2*i]}}} : {4{carry[2*i]}};
                end
            end
            VSEW_32: begin
                for (int i = 0; i < ALU_OP_W / 32; i++) begin
                    satval_d[8*i +: 8] = mode_signed ? {~sig_res[4*i], {7{sig_res[4*i]}}} : {8{carry[4*i]}};
                end
            end
            default: ;
        endcase
    end

    // barrel shifter
    logic shift_arith;
    always_comb begin
        shift_arith = DONT_CARE_ZERO ? '0 : 'x;
        unique case (state_ex1_q.mode.opx1.shift)
            ALU_SHIFT_VSRL: shift_arith = 1'b0;
            ALU_SHIFT_VSRA: shift_arith = 1'b1;
            default: ;
        endcase
    end
    logic [ALU_OP_W  -1:0] shift_left;
    logic [ALU_OP_W*2-1:0] shift_right;
    always_comb begin
        shift_left  = DONT_CARE_ZERO ? '0 : 'x;
        shift_right = DONT_CARE_ZERO ? '0 : 'x;
        unique case (state_ex1_q.eew)

            VSEW_8: begin
                for (int i = 0; i < ALU_OP_W / 8; i++) begin
                    shift_left [8 *i +: 8 ] =  operand2_32[8 *i +: 8 ]         <<        operand1_32[8 *i +: 3];
                    shift_right[16*i +: 16] = {operand2_32[8 *i +: 8 ], 8'b0 } >> {1'b0, operand1_32[8 *i +: 3]};
                    for (int j = 0; j < operand1_32[8 *i +: 3]; j++) begin
                        shift_right[16*i+15-j] = shift_arith & operand2_32[8 *i+7 ]; // sign extend
                    end
                end
            end

            VSEW_16: begin
                for (int i = 0; i < ALU_OP_W / 16; i++) begin
                    shift_left [16*i +: 16] =  operand2_32[16*i +: 16]         <<        operand1_32[16*i +: 4];
                    shift_right[32*i +: 32] = {operand2_32[16*i +: 16], 16'b0} >> {1'b0, operand1_32[16*i +: 4]};
                    for (int j = 0; j < operand1_32[16*i +: 4]; j++) begin
                        shift_right[32*i+31-j] = shift_arith & operand2_32[16*i+15]; // sign extend
                    end
                end
            end

            VSEW_32: begin
                for (int i = 0; i < ALU_OP_W / 32; i++) begin
                    shift_left [32*i +: 32] =  operand2_32[32*i +: 32]         <<        operand1_32[32*i +: 5];
                    shift_right[64*i +: 64] = {operand2_32[32*i +: 32], 32'b0} >> {1'b0, operand1_32[32*i +: 5]};
                    for (int j = 0; j < operand1_32[32*i +: 5]; j++) begin
                        shift_right[64*i+63-j] = shift_arith & operand2_32[32*i+31]; // sign extend
                    end
                end
            end

            default: ;
        endcase
    end
    always_comb begin
        shift_res_d = DONT_CARE_ZERO ? '0 : 'x;
        unique case ({state_ex1_q.mode.opx1.shift, state_ex1_q.eew})

            {ALU_SHIFT_VSLL, VSEW_8 },
            {ALU_SHIFT_VSLL, VSEW_16},
            {ALU_SHIFT_VSLL, VSEW_32}: begin
                shift_res_d = shift_left;
            end

            {ALU_SHIFT_VSRL, VSEW_8},
            {ALU_SHIFT_VSRA, VSEW_8}: begin
                for (int i = 0; i < ALU_OP_W / 8 ; i++) begin
                    unique case (state_ex1_q.vxrm)
                        VXRM_RNU: shift_res_d[8 *i +: 8 ] = shift_right[16*i+8  +: 8 ] + {7'b0 ,  shift_right[16*i+7 ]};
                        VXRM_RNE: shift_res_d[8 *i +: 8 ] = shift_right[16*i+8  +: 8 ] + {7'b0 ,  shift_right[16*i+7 ] & ((shift_right[16*i +: 7 ] != '0) | shift_right[16*i+8 ])};
                        VXRM_RDN: shift_res_d[8 *i +: 8 ] = shift_right[16*i+8  +: 8 ];
                        VXRM_ROD: shift_res_d[8 *i +: 8 ] = shift_right[16*i+8  +: 8 ] + {7'b0 , ~shift_right[16*i+8 ] & ( shift_right[16*i +: 8 ] != '0)};
                        default: ;
                    endcase
                end
            end
            {ALU_SHIFT_VSRL, VSEW_16},
            {ALU_SHIFT_VSRA, VSEW_16}: begin
                for (int i = 0; i < ALU_OP_W / 16; i++) begin
                    unique case (state_ex1_q.vxrm)
                        VXRM_RNU: shift_res_d[16*i +: 16] = shift_right[32*i+16 +: 16] + {15'b0,  shift_right[32*i+15]};
                        VXRM_RNE: shift_res_d[16*i +: 16] = shift_right[32*i+16 +: 16] + {15'b0,  shift_right[32*i+15] & ((shift_right[32*i +: 15] != '0) | shift_right[32*i+16])};
                        VXRM_RDN: shift_res_d[16*i +: 16] = shift_right[32*i+16 +: 16];
                        VXRM_ROD: shift_res_d[16*i +: 16] = shift_right[32*i+16 +: 16] + {15'b0, ~shift_right[32*i+16] & ( shift_right[32*i +: 16] != '0)};
                        default: ;
                    endcase
                end
            end
            {ALU_SHIFT_VSRL, VSEW_32},
            {ALU_SHIFT_VSRA, VSEW_32}: begin
                for (int i = 0; i < ALU_OP_W / 32; i++) begin
                    unique case (state_ex1_q.vxrm)
                        VXRM_RNU: shift_res_d[32*i +: 32] = shift_right[64*i+32 +: 32] + {31'b0,  shift_right[64*i+31]};
                        VXRM_RNE: shift_res_d[32*i +: 32] = shift_right[64*i+32 +: 32] + {31'b0,  shift_right[64*i+31] & ((shift_right[64*i +: 31] != '0) | shift_right[64*i+32])};
                        VXRM_RDN: shift_res_d[32*i +: 32] = shift_right[64*i+32 +: 32];
                        VXRM_ROD: shift_res_d[32*i +: 32] = shift_right[64*i+32 +: 32] + {31'b0, ~shift_right[64*i+32] & ( shift_right[64*i +: 32] != '0)};
                        default: ;
                    endcase
                end
            end

            default: ;
        endcase
    end

    // arithmetic result
    always_comb begin
        result_alu_d = DONT_CARE_ZERO ? '0 : 'x;
        unique case (state_ex2_q.mode.opx2.res)
            ALU_VADD: begin
                for (int i = 0; i < ALU_OP_W / 8; i++) begin
                    result_alu_d[8*i +: 8] = sum_q[9*i +: 8];
                end
            end

            // saturating add: the result is replaced by the saturation value
            // if the corresponding bit in the compare register is set
            ALU_VSADD: begin
                for (int i = 0; i < ALU_OP_W / 8; i++) begin
                    result_alu_d[8*i +: 8] = cmp_q[i] ? {satval_q[2*i+1], {7{satval_q[2*i]}}} : sum_q[9*i +: 8];
                end
            end

            ALU_VAND:   result_alu_d = operand2_tmp_q & operand1_tmp_q;
            ALU_VOR:    result_alu_d = operand2_tmp_q | operand1_tmp_q;
            ALU_VXOR:   result_alu_d = operand2_tmp_q ^ operand1_tmp_q;
            ALU_VSHIFT: result_alu_d = shift_res_q;

            // select either one of the operands based on the register `cmp_q',
            // which holds the result of a comparison for the vmin[u].* and
            // vmax[u].* instructions, the v0 mask for vmerge.*, or all zeroes
            // for the vsext.* and vzext.* instructions which use vs2 as source
            ALU_VSEL: begin
                for (int i = 0; i < ALU_OP_W / 8; i++) begin
                    result_alu_d[8*i +: 8] = cmp_q[i] ? ~operand1_tmp_q[8*i +: 8] : operand2_tmp_q[8*i +: 8];
                end
            end
            ALU_VSELN: begin
                for (int i = 0; i < ALU_OP_W / 8; i++) begin
                    result_alu_d[8*i +: 8] = cmp_q[i] ? operand2_tmp_q[8*i +: 8] : ~operand1_tmp_q[8*i +: 8];
                end
            end
            default: ;
        endcase
    end

    // compare result; comparisons are done using the compare register `cmp_q';
    // equality (or inequality) is determined by testing whether the sum is 0
    logic [ALU_OP_W/8-1:0] neq;
    always_comb begin
        neq = DONT_CARE_ZERO ? '0 : 'x;
        unique case (state_ex2_q.eew)
            VSEW_8: begin
                for (int i = 0; i < ALU_OP_W / 8 ; i++) begin
                    neq[i  ] = | sum_q[9 *i    +: 8];
                end
            end
            VSEW_16: begin
                for (int i = 0; i < ALU_OP_W / 16; i++) begin
                    neq[2*i] = |{sum_q[18*i+9  +: 8], sum_q[18*i    +: 8]};
                end
            end
            VSEW_32: begin
                for (int i = 0; i < ALU_OP_W / 32; i++) begin
                    neq[4*i] = |{sum_q[36*i+27 +: 8], sum_q[36*i+18 +: 8], sum_q[36*i+9 +: 8], sum_q[36*i +: 8]};
                end
            end
            default: ;
        endcase
    end
    always_comb begin
        result_cmp_d = DONT_CARE_ZERO ? '0 : 'x;
        unique case (state_ex2_q.mode.opx2.cmp)
            ALU_CMP_CMP:  result_cmp_d =  cmp_q;
            ALU_CMP_CMPN: result_cmp_d = ~cmp_q;
            ALU_CMP_EQ:   result_cmp_d = ~neq;
            ALU_CMP_NE:   result_cmp_d =  neq;
            default: ;
        endcase
    end


`ifdef VPROC_SVA
`include "vproc_alu_sva.svh"
`endif

endmodule
