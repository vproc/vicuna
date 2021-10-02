// Copyright TU Wien
// Licensed under the ISC license, see LICENSE.txt for details
// SPDX-License-Identifier: ISC


`include "vproc_vregshift.svh"

module vproc_mul #(
        parameter int unsigned        VREG_W,               // width in bits of vector registers
        parameter int unsigned        VMSK_W,               // width of vector register masks (= VREG_W / 8)
        parameter int unsigned        CFG_VL_W,
        parameter int unsigned        MUL_OP_W,             // MUL unit operand size
        parameter int unsigned        MAX_WR_ATTEMPTS = 1,
        parameter vproc_pkg::mul_type MUL_TYPE        = vproc_pkg::MUL_GENERIC,
        parameter bit                 BUF_VREG        = 1'b1,
        parameter bit                 BUF_OPERANDS    = 1'b1, // buffer operands in registers
        parameter bit                 BUF_RESULTS     = 1'b1, // buffer result in registers
        parameter bit                 BUF_MUL_IN      = 1'b1, // buffer multiplier input in registers
        parameter bit                 BUF_MUL_OUT     = 1'b1, // buffer multiplier output in registers
        parameter bit                 COMB_INIT_ZERO  = 1'b0,
        parameter bit                 ASYNC_RESET     = 1'b0
    )(
        input  logic                  clk_i,
        input  logic                  rst_ni,

        input  vproc_pkg::cfg_vsew    vsew_i,
        input  vproc_pkg::cfg_lmul    lmul_i,
        input  logic [CFG_VL_W-1:0]   vl_i,
        input  logic                  vl_0_i,

        input  logic                  op_rdy_i,
        output logic                  op_ack_o,

        input  vproc_pkg::op_mode_mul mode_i,
        input                         widening_i,
        input  vproc_pkg::op_regs     rs1_i,
        input  logic [4:0]            vs2_i,
        input  logic [4:0]            vd_i,

        output logic [31:0]           clear_rd_hazards_o,
        output logic [31:0]           clear_wr_hazards_o,

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

    // max number of cycles by which a write can be delayed
    localparam int unsigned MAX_WR_DELAY = (1 << MAX_WR_ATTEMPTS) - 1;


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
        logic                busy;
        logic                first_cycle;
        logic                last_cycle;
        op_mode_mul          mode;
        cfg_vsew             eew;        // effective element width
        cfg_emul             emul;       // effective MUL factor
        logic [CFG_VL_W-1:0] vl;
        logic                vl_0;
        vproc_pkg::op_regs   rs1;
        logic                vs1_narrow;
        logic                vs1_fetch;
        logic                vs1_shift;
        logic [4:0]          vs2;
        logic                vs2_narrow;
        logic                vs2_fetch;
        logic                vs2_shift;
        logic                v0msk_shift;
        logic [4:0]          vs3;
        logic                vs3_fetch;
        logic [4:0]          vd;
        logic                vd_store;
    } mul_state;

    mul_state state_q, state_d;

    generate
        if (ASYNC_RESET) begin
            always_ff @(posedge clk_i or negedge rst_ni) begin : vproc_mul_state
                if (!rst_ni) begin
                    state_q <= '{busy: 1'b0, default: 'x};
                end else begin
                    state_q <= state_d;
                end
            end
        end else begin
            always_ff @(posedge clk_i) begin : vproc_mul_state
                state_q          <= state_d;
                if (!rst_ni) begin
                    state_q.busy <= 1'b0;
                end
            end
        end
    endgenerate

    logic last_cycle;
    always_comb begin
        last_cycle = COMB_INIT_ZERO ? 1'b0 : 1'bx;
        unique case (state_q.emul)
            EMUL_1: last_cycle =                                        state_q.count.part.low == '1;
            EMUL_2: last_cycle = (state_q.count.part.mul[  0] == '1) & (state_q.count.part.low == '1);
            EMUL_4: last_cycle = (state_q.count.part.mul[1:0] == '1) & (state_q.count.part.low == '1);
            EMUL_8: last_cycle = (state_q.count.part.mul[2:0] == '1) & (state_q.count.part.low == '1);
        endcase
    end

    always_comb begin
        op_ack_o = 1'b0;
        state_d  = state_q;

        if (((~state_q.busy) | last_cycle) & op_rdy_i) begin
            op_ack_o            = 1'b1;
            state_d.count.val   = '0;
            state_d.busy        = 1'b1;
            state_d.first_cycle = 1'b1;
            state_d.mode        = mode_i;
            state_d.emul        = COMB_INIT_ZERO ? cfg_emul'('0) : cfg_emul'('x);
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
            state_d.vs2        = mode_i.op2_is_vd ? vd_i : vs2_i;
            state_d.vs2_narrow = widening_i;
            state_d.vs2_fetch  = 1'b1;
            state_d.vs2_shift  = 1'b1;
            state_d.v0msk_shift = 1'b1;
            state_d.vs3        = mode_i.op2_is_vd ? vs2_i : vd_i;
            state_d.vs3_fetch  = mode_i.op == MUL_VMACC;
            state_d.vd         = vd_i;
            state_d.vd_store   = 1'b0;
        end
        else if (state_q.busy) begin
            state_d.count.val   = state_q.count.val + 1;
            state_d.busy        = ~last_cycle;
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
                    state_d.vs2[2:0]  = state_q.vs2[2:0] + 3'b1;
                    state_d.vs2_fetch = 1'b1;
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
    mul_state state_init, state_vreg_q, state_vs1_q, state_vs2_q, state_ex1_q, state_ex2_q, state_ex3_q, state_res_q, state_vd_q;
    always_comb begin
        state_init            = state_q;
        state_init.last_cycle = state_q.busy & last_cycle;
        state_init.vd_store   = state_q.count.part.low == '1;
    end

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
    logic              vreg_wr_en_q  [MAX_WR_DELAY], vreg_wr_en_d;
    logic [4:0]        vreg_wr_addr_q[MAX_WR_DELAY], vreg_wr_addr_d;
    logic [VMSK_W-1:0] vreg_wr_mask_q[MAX_WR_DELAY], vreg_wr_mask_d;
    logic [VREG_W-1:0] vreg_wr_q     [MAX_WR_DELAY], vreg_wr_d;

    // hazard clear registers
    logic [31:0] clear_rd_hazards_q, clear_rd_hazards_d;
    logic [31:0] clear_wr_hazards_q, clear_wr_hazards_d;

    generate
        if (BUF_VREG) begin
            always_ff @(posedge clk_i) begin : vproc_mul_stage_vreg
                state_vreg_q <= state_init;
                vreg_rd_q    <= vreg_rd_d;
            end
        end else begin
            always_comb begin
                state_vreg_q = state_init;
                vreg_rd_q    = vreg_rd_d;
            end
        end

        always_ff @(posedge clk_i) begin : vproc_mul_stage_vs1
            state_vs1_q <= state_vreg_q;
            vs1_shift_q <= vs1_shift_d;
        end

        always_ff @(posedge clk_i) begin : vproc_mul_stage_vs2
            state_vs2_q   <= state_vs1_q;
            vs2_shift_q   <= vs2_shift_d;
            vs3_shift_q   <= vs3_shift_d;
            v0msk_shift_q <= v0msk_shift_d;
            vs1_tmp_q     <= vs1_tmp_d;
        end

        if (BUF_OPERANDS) begin
            always_ff @(posedge clk_i) begin : vproc_mul_stage_ex1
                state_ex1_q    <= state_vs2_q;
                operand1_q     <= operand1_d;
                operand2_q     <= operand2_d;
                operand_mask_q <= operand_mask_d;
                accumulator1_q <= accumulator1_d;
            end
        end else begin
            always_comb begin
                state_ex1_q    = state_vs2_q;
                operand1_q     = operand1_d;
                operand2_q     = operand2_d;
                operand_mask_q = operand_mask_d;
                accumulator1_q = accumulator1_d;
            end
        end

        if (BUF_MUL_IN) begin
            always_ff @(posedge clk_i) begin : vproc_mul_stage_ex2
                state_ex2_q    <= state_ex1_q;
                accumulator2_q <= accumulator2_d;
                result_mask1_q <= result_mask1_d;
            end
        end else begin
            always_comb begin
                state_ex2_q    = state_ex1_q;
                accumulator2_q = accumulator2_d;
                result_mask1_q = result_mask1_d;
            end
        end

        if (BUF_MUL_OUT) begin
            always_ff @(posedge clk_i) begin : vproc_mul_stage_ex3
                state_ex3_q    <= state_ex2_q;
                result_mask2_q <= result_mask2_d;
            end
        end else begin
            always_comb begin
                state_ex3_q    = state_ex2_q;
                result_mask2_q = result_mask2_d;
            end
        end

        if (BUF_RESULTS) begin
            always_ff @(posedge clk_i) begin : vproc_mul_stage_res
                state_res_q    <= state_ex3_q;
                result_q       <= result_d;
                result_mask3_q <= result_mask3_d;
            end
        end else begin
            always_comb begin
                state_res_q    = state_ex3_q;
                result_q       = result_d;
                result_mask3_q = result_mask3_d;
            end
        end

        always_ff @(posedge clk_i) begin : vproc_mul_stage_vd
            state_vd_q    <= state_res_q;
            vd_shift_q    <= vd_shift_d;
            vdmsk_shift_q <= vdmsk_shift_d;
        end

        if (MAX_WR_DELAY > 0) begin
            always_ff @(posedge clk_i) begin : vproc_mul_wr_delay
                vreg_wr_en_q  [0] = vreg_wr_en_d;
                vreg_wr_addr_q[0] = vreg_wr_addr_d;
                vreg_wr_mask_q[0] = vreg_wr_mask_d;
                vreg_wr_q     [0] = vreg_wr_d;
                for (int i = 1; i < MAX_WR_DELAY; i++) begin
                    vreg_wr_en_q  [i] = vreg_wr_en_q  [i-1];
                    vreg_wr_addr_q[i] = vreg_wr_addr_q[i-1];
                    vreg_wr_mask_q[i] = vreg_wr_mask_q[i-1];
                    vreg_wr_q     [i] = vreg_wr_q     [i-1];
                end
            end
        end

        always_ff @(posedge clk_i) begin
            clear_rd_hazards_q <= clear_rd_hazards_d;
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

    // read hazard clearing
    // note that vs1 and vs2 are always of the same width; vs3 may be wider for
    // widening multiply-add instructions, but then vs3 == vd and hence vs3
    // cannot overlap with vs1 and vs2; therefore, if any of vs1, vs2 or vs3
    // overlap, then they are of the same width and read simultaneously
    assign clear_rd_hazards_d = state_init.busy ? (
        (state_init.vs1_fetch ? (32'b1 << state_init.rs1.r.vaddr) : 32'b0) |
        (state_init.vs2_fetch ? (32'b1 << state_init.vs2        ) : 32'b0) |
        (state_init.vs3_fetch ? (32'b1 << state_init.vs3        ) : 32'b0) |
        {31'b0, state_init.mode.masked & state_init.first_cycle}
    ) : 32'b0;
    assign clear_rd_hazards_o = clear_rd_hazards_q;


    ///////////////////////////////////////////////////////////////////////////
    // MUL REGISTER READ/WRITE:

    // source register addressing and read:
    assign vreg_rd_addr_o = (state_init.count.part.low[0] == 1'b0) ? state_init.rs1.r.vaddr : state_init.vs2;
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
        .COMB_INIT_ZERO ( COMB_INIT_ZERO                )
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
    assign vreg_wr_en_d   = state_vd_q.busy & state_vd_q.vd_store;
    assign vreg_wr_addr_d = state_vd_q.vd;
    assign vreg_wr_mask_d = vreg_wr_en_o ? vdmsk_shift_q : '0;
    assign vreg_wr_d      = vd_shift_q;


    ///////////////////////////////////////////////////////////////////////////
    // MUL ARITHMETIC:

    logic [MUL_OP_W/8-1:0] op1_signs, op2_signs;
    always_comb begin
        op1_signs = COMB_INIT_ZERO ? '0 : 'x;
        op2_signs = COMB_INIT_ZERO ? '0 : 'x;
        for (int i = 0; i < MUL_OP_W/8; i++) begin
            op1_signs[i] = state_ex1_q.mode.op1_signed & operand1_q[8*i+7];
            op2_signs[i] = state_ex1_q.mode.op2_signed & operand2_q[8*i+7];
        end
    end

    logic ex1_vsew_8, ex1_vsew_32;
    always_comb begin
        ex1_vsew_8  = COMB_INIT_ZERO ? '0 : 'x;
        ex1_vsew_32 = COMB_INIT_ZERO ? '0 : 'x;
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
        mul_op1 = COMB_INIT_ZERO ? '0 : 'x;
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
        mul_op2 = COMB_INIT_ZERO ? '0 : 'x;
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
        accumulator2_d = COMB_INIT_ZERO ? '0 : 'x;
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
        ex2_vsew_8  = COMB_INIT_ZERO ? '0 : 'x;
        ex2_vsew_16 = COMB_INIT_ZERO ? '0 : 'x;
        ex2_vsew_32 = COMB_INIT_ZERO ? '0 : 'x;
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
        mul_acc = COMB_INIT_ZERO ? '0 : 'x;
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
        mul_accflag = COMB_INIT_ZERO ? '0 : 'x;
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
                .MUL_TYPE    ( MUL_TYPE                ),
                .BUF_OPS     ( BUF_MUL_IN              ),
                .BUF_MUL     ( BUF_MUL_OUT             ),
                .BUF_RES     ( 1'b0                    )
            ) mul_block (
                .clk_i       ( clk_i                   ),
                .rst_ni      ( rst_ni                  ),
                .op1_i       ( mul_op1    [17*g +: 17] ),
                .op2_i       ( mul_op2    [17*g +: 17] ),
                .acc_i       ( mul_acc    [16*g +: 16] ),
                .acc_flag_i  ( mul_accflag             ),
                .acc_sub_i   ( mul_accsub              ),
                .res_o       ( mul_res    [33*g +: 33] )
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
        result_d = COMB_INIT_ZERO ? '0 : 'x;
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

endmodule
