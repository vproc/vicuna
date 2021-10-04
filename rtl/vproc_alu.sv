// Copyright TU Wien
// Licensed under the ISC license, see LICENSE.txt for details
// SPDX-License-Identifier: ISC


`include "vproc_vregshift.svh"

module vproc_alu #(
        parameter int unsigned          VREG_W,                 // width in bits of vector registers
        parameter int unsigned          VMSK_W,                 // width of vector register masks (= VREG_W / 8)
        parameter int unsigned          CFG_VL_W,
        parameter int unsigned          ALU_OP_W,               // ALU operand size
        parameter int unsigned          MAX_WR_ATTEMPTS  = 1,
        parameter bit                   BUF_VREG         = 1'b1,
        parameter bit                   BUF_OPERANDS     = 1'b1, // buffer operands in registers
        parameter bit                   BUF_INTERMEDIATE = 1'b1,
        parameter bit                   BUF_RESULTS      = 1'b1, // buffer results in registers
        parameter bit                   COMB_INIT_ZERO   = 1'b0
    )(
        input  logic                    clk_i,
        input  logic                    async_rst_ni,
        input  logic                    sync_rst_ni,

        input  vproc_pkg::cfg_vsew      vsew_i,
        input  vproc_pkg::cfg_lmul      lmul_i,
        input  logic [CFG_VL_W-1:0]     vl_i,
        input  logic                    vl_0_i,

        input  logic                    op_rdy_i,
        output logic                    op_ack_o,

        input  vproc_pkg::op_mode_alu   mode_i,
        input  vproc_pkg::op_widenarrow widenarrow_i,
        input  vproc_pkg::op_regs       rs1_i,
        input  logic [4:0]              vs2_i,
        input  logic                    vs2_vreg_i,
        input  logic [4:0]              vd_i,

        output logic [31:0]             clear_rd_hazards_o,
        output logic [31:0]             clear_wr_hazards_o,

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

    // max number of cycles by which a write can be delayed
    localparam int unsigned MAX_WR_DELAY = (1 << MAX_WR_ATTEMPTS) - 1;


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
        logic                busy;
        logic                first_cycle;
        logic                last_cycle;
        op_mode_alu          mode;
        logic                subtract;   // set if an operand is inverted
        cfg_vsew             eew;        // effective element width
        cfg_emul             emul;       // effective MUL factor
        logic [CFG_VL_W-1:0] vl;
        logic                vl_0;
        vproc_pkg::op_regs   rs1;
        logic                vs1_narrow;
        logic                vs1_fetch;
        logic                vs1_shift;
        logic [4:0]          vs2;
        logic                vs2_vreg;
        logic                vs2_narrow;
        logic                vs2_fetch;
        logic                vs2_shift;
        logic                v0msk_shift;
        logic [4:0]          vd;
        logic                vd_narrow;
        logic                vd_store;
    } alu_state;

    alu_state state_q, state_d;
    always_ff @(posedge clk_i or negedge async_rst_ni) begin : vproc_alu_state
        if (~async_rst_ni) begin
            state_q <= '{busy: 1'b0, default: 'x};
        end else begin
            state_q <= state_d;
            if (~sync_rst_ni) begin
                state_q.busy <= 1'b0;
            end
        end
    end

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
            state_d.subtract    = mode_i.inv_op1 | mode_i.inv_op2;
            // for widening or narrowing ops, eew and emul are increased to the next higher value,
            // since those are the eew and emul that are used for the op itself; vl is doubled to
            // capture the wider byte width of the intermediate result
            state_d.emul = COMB_INIT_ZERO ? cfg_emul'('0) : cfg_emul'('x);
            if (widenarrow_i == OP_SINGLEWIDTH) begin
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
            if (mode_i.op_mask == ALU_MASK_ARIT) begin
                state_d.emul = EMUL_1; // mask arithmetic always uses EMUL == 1
            end
            state_d.vl_0       = vl_0_i;
            state_d.rs1        = rs1_i;
            state_d.vs1_narrow = (widenarrow_i == OP_WIDENING) | (widenarrow_i == OP_WIDENING_VS2);
            state_d.vs1_fetch  = rs1_i.vreg;
            state_d.vs1_shift  = 1'b1;
            state_d.vs2        = vs2_i;
            state_d.vs2_vreg   = vs2_vreg_i;
            state_d.vs2_narrow = widenarrow_i == OP_WIDENING;
            state_d.vs2_fetch  = vs2_vreg_i;
            state_d.vs2_shift  = 1'b1;
            state_d.v0msk_shift = 1'b1;
            state_d.vd         = vd_i;
            state_d.vd_narrow  = widenarrow_i == OP_NARROWING;
            state_d.vd_store   = 1'b0;
        end
        else if (state_q.busy) begin
            state_d.count.val   = state_q.count.val + 1;
            state_d.busy        = ~last_cycle;
            state_d.first_cycle = 1'b0;
            state_d.vs1_fetch   = 1'b0;
            state_d.vs2_fetch   = 1'b0;
            if (state_q.count.part.low == '1) begin
                if (state_q.rs1.vreg & (~state_q.vs1_narrow | state_q.count.part.mul[0])) begin
                    state_d.rs1.r.vaddr[2:0] = state_q.rs1.r.vaddr[2:0] + 3'b1;
                    state_d.vs1_fetch        = state_q.rs1.vreg;
                end
                if (~state_q.vs2_narrow | state_q.count.part.mul[0]) begin
                    state_d.vs2[2:0]  = state_q.vs2[2:0] + 3'b1;
                    state_d.vs2_fetch = state_q.vs2_vreg;
                end
                if (~state_q.mode.cmp & (~state_q.vd_narrow | state_q.count.part.mul[0])) begin
                    state_d.vd[2:0] = state_q.vd[2:0] + 3'b1;
                end
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
    // ALU PIPELINE BUFFERS:

    // pass state information along pipeline:
    alu_state state_init, state_vreg_q, state_vs1_q, state_vs2_q, state_ex1_q, state_ex2_q, state_ex3_q, state_res_q, state_vd_q;
    always_comb begin
        state_init            = state_q;
        state_init.last_cycle = state_q.busy & last_cycle;
        state_init.vd_store   = (state_q.count.part.low == '1) & (~state_q.vd_narrow | state_q.count.part.mul[0]);
    end

    // common vreg read register:
    logic [VREG_W-1:0] vreg_rd_q, vreg_rd_d;

    // operand shift registers:
    logic [VREG_W-1:0] vs1_shift_q,   vs1_shift_d;
    logic [VREG_W-1:0] vs2_shift_q,   vs2_shift_d;
    logic [VREG_W-1:0] v0msk_shift_q, v0msk_shift_d;

    // temporary buffer for vs1 while fetching vs2:
    logic [ALU_OP_W-1:0] vs1_tmp_q, vs1_tmp_d;

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

    // result shift register:
    logic [VREG_W-1:0] vd_alu_shift_q,    vd_alu_shift_d;
    logic [VMSK_W-1:0] vdmsk_alu_shift_q, vdmsk_alu_shift_d;
    logic [VMSK_W-1:0] vd_cmp_shift_q,    vd_cmp_shift_d;
    logic [VMSK_W-1:0] vdmsk_cmp_q,       vdmsk_cmp_d;

    // vreg write buffers
    logic              vreg_wr_en_q  [MAX_WR_DELAY], vreg_wr_en_d;
    logic              vreg_wr_last_q[MAX_WR_DELAY], vreg_wr_last_d;
    logic [4:0]        vreg_wr_addr_q[MAX_WR_DELAY], vreg_wr_addr_d;
    logic [VMSK_W-1:0] vreg_wr_mask_q[MAX_WR_DELAY], vreg_wr_mask_d;
    logic [VREG_W-1:0] vreg_wr_q     [MAX_WR_DELAY], vreg_wr_d;

    // hazard clear registers
    logic [31:0] clear_rd_hazards_q, clear_rd_hazards_d;
    logic [31:0] clear_wr_hazards_q, clear_wr_hazards_d;

    generate
        if (BUF_VREG) begin
            always_ff @(posedge clk_i) begin : vproc_alu_stage_vreg
                state_vreg_q <= state_init;
                vreg_rd_q    <= vreg_rd_d;
            end
        end else begin
            always_comb begin
                state_vreg_q = state_init;
                vreg_rd_q    = vreg_rd_d;
            end
        end

        always_ff @(posedge clk_i) begin : vproc_alu_stage_vs1
            state_vs1_q <= state_vreg_q;
            vs1_shift_q <= vs1_shift_d;
        end

        always_ff @(posedge clk_i) begin : vproc_alu_stage_vs2
            state_vs2_q   <= state_vs1_q;
            vs2_shift_q   <= vs2_shift_d;
            v0msk_shift_q <= v0msk_shift_d;
            vs1_tmp_q     <= vs1_tmp_d;
        end

        if (BUF_OPERANDS) begin
            always_ff @(posedge clk_i) begin : vproc_alu_stage_ex1
                state_ex1_q    <= state_vs2_q;
                operand1_q     <= operand1_d;
                operand2_q     <= operand2_d;
                operand_mask_q <= operand_mask_d;
            end
        end else begin
            always_comb begin
                state_ex1_q    = state_vs2_q;
                operand1_q     = operand1_d;
                operand2_q     = operand2_d;
                operand_mask_q = operand_mask_d;
            end
        end

        if (BUF_INTERMEDIATE) begin
            always_ff @(posedge clk_i) begin : vproc_alu_stage_ex2
                state_ex2_q    <= state_ex1_q;
                operand1_tmp_q <= operand1_tmp_d;
                operand2_tmp_q <= operand2_tmp_d;
                operand_mask_tmp_q <= operand_mask_tmp_d;
                sum_q          <= sum_d;
                cmp_q          <= cmp_d;
                satval_q       <= satval_d;
                shift_res_q    <= shift_res_d;
            end
        end else begin
            always_comb begin
                state_ex2_q    = state_ex1_q;
                operand1_tmp_q = operand1_tmp_d;
                operand2_tmp_q = operand2_tmp_d;
                operand_mask_tmp_q = operand_mask_tmp_d;
                sum_q          = sum_d;
                cmp_q          = cmp_d;
                satval_q       = satval_d;
                shift_res_q    = shift_res_d;
            end
        end

        if (BUF_RESULTS) begin
            always_ff @(posedge clk_i) begin : vproc_alu_stage_res
                state_res_q   <= state_ex2_q;
                result_alu_q  <= result_alu_d;
                result_cmp_q  <= result_cmp_d;
                result_mask_q <= result_mask_d;
            end
        end else begin
            always_comb begin
                state_res_q   = state_ex2_q;
                result_alu_q  = result_alu_d;
                result_cmp_q  = result_cmp_d;
                result_mask_q = result_mask_d;
            end
        end

        always_ff @(posedge clk_i) begin : vproc_alu_stage_vd
            state_vd_q        <= state_res_q;
            vd_alu_shift_q    <= vd_alu_shift_d;
            vdmsk_alu_shift_q <= vdmsk_alu_shift_d;
            vd_cmp_shift_q    <= vd_cmp_shift_d;
            vdmsk_cmp_q       <= vdmsk_cmp_d;
        end

        if (MAX_WR_DELAY > 0) begin
            always_ff @(posedge clk_i) begin : vproc_alu_wr_delay
                vreg_wr_en_q  [0] = vreg_wr_en_d;
                vreg_wr_last_q[0] = vreg_wr_last_d;
                vreg_wr_addr_q[0] = vreg_wr_addr_d;
                vreg_wr_mask_q[0] = vreg_wr_mask_d;
                vreg_wr_q     [0] = vreg_wr_d;
                for (int i = 1; i < MAX_WR_DELAY; i++) begin
                    vreg_wr_en_q  [i] = vreg_wr_en_q  [i-1];
                    vreg_wr_last_q[i] = vreg_wr_last_q[i-1];
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
        clear_wr_hazards_d     = vreg_wr_last_d                 ? (32'b1 << vreg_wr_addr_d                ) : 32'b0;
        if (MAX_WR_DELAY > 0) begin
            clear_wr_hazards_d = vreg_wr_last_q[MAX_WR_DELAY-1] ? (32'b1 << vreg_wr_addr_q[MAX_WR_DELAY-1]) : 32'b0;
        end
    end
    assign clear_wr_hazards_o = clear_wr_hazards_q;

    // read hazard clearing
    // TODO figure out what to do when mode is OP_WIDENING_VS2 and vs1 == vs2;
    // in that situation we need to delay clearing of some vregs of the vs2 group,
    // but not all vregs of vs2 also appear in vs1
    logic vs2_equals_vs1;
    //assign vs2_equals_vs1 = state_init.rs1.vreg & (state_init.rs1.r.vaddr == state_init.vs2);
    assign vs2_equals_vs1 = '0;
    assign clear_rd_hazards_d = state_init.busy ? (
        ( state_init.vs1_fetch                    ? (32'b1 << state_init.rs1.r.vaddr) : 32'b0) |
        ((state_init.vs2_fetch & ~vs2_equals_vs1) ? (32'b1 << state_init.vs2        ) : 32'b0) |
        {31'b0, (state_init.mode.masked | (state_init.mode.op_mask == ALU_MASK_CARRY) | (state_init.mode.op_mask == ALU_MASK_SEL)) & state_init.first_cycle}
    ) : 32'b0;
    assign clear_rd_hazards_o = clear_rd_hazards_q;


    ///////////////////////////////////////////////////////////////////////////
    // ALU REGISTER READ/WRITE AND CONVERSION

    // source register addressing and read:
    assign vreg_rd_addr_o = (state_init.count.part.low[0] == 1'b0) ? state_init.rs1.r.vaddr : state_init.vs2;
    assign vreg_rd_d      = vreg_rd_i;

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
    `VREGSHIFT_OPERAND_NARROW(VREG_W, ALU_OP_W, vs1_info, vreg_rd_q, vs1_shift_q, vs1_shift_d)
    `VREGSHIFT_OPERAND_NARROW(VREG_W, ALU_OP_W, vs2_info, vreg_rd_q, vs2_shift_q, vs2_shift_d)
    `VREGSHIFT_OPMASK(VREG_W, ALU_OP_W, v0msk_info, state_vs1_q.eew, vreg_mask_i, v0msk_shift_q, v0msk_shift_d)
    assign vs1_tmp_d = vs1_shift_q[ALU_OP_W-1:0];

    // conversion from source registers to operands:
    logic [ALU_OP_W-1:0] operand1, operand2;
    vproc_vregunpack #(
        .OP_W           ( ALU_OP_W                      ),
        .COMB_INIT_ZERO ( COMB_INIT_ZERO                )
    ) alu_vregunpack (
        .vsew_i         ( state_vs2_q.eew               ),
        .rs1_i          ( state_vs2_q.rs1               ),
        .vs1_i          ( vs1_tmp_q                     ),
        .vs1_narrow_i   ( state_vs2_q.vs1_narrow        ),
        .vs1_sigext_i   ( state_vs2_q.mode.sigext       ),
        .vs2_i          ( vs2_shift_q[ALU_OP_W-1:0]     ),
        .vs2_narrow_i   ( state_vs2_q.vs2_narrow        ),
        .vs2_sigext_i   ( state_vs2_q.mode.sigext       ),
        .vmsk_i         ( v0msk_shift_q[ALU_OP_W/8-1:0] ),
        .operand1_o     ( operand1                      ),
        .operand2_o     (                               ),
        .operand_mask_o ( operand_mask_d                )
    );
    always_comb begin
        operand2 = vs2_shift_q[ALU_OP_W-1:0];
        if (state_vs2_q.vs2_narrow) begin
            operand2 = COMB_INIT_ZERO ? '0 : 'x;
            unique case (state_vs2_q.eew)
                VSEW_16: begin
                    for (int i = 0; i < ALU_OP_W / 16; i++) begin
                        operand2[16*i +: 16] = {{8 {state_vs2_q.mode.sigext & vs2_shift_q[8 *i + 7 ]}}, vs2_shift_q[8 *i +: 8 ]};
                    end
                end
                VSEW_32: begin
                    for (int i = 0; i < ALU_OP_W / 32; i++) begin
                        operand2[32*i +: 32] = {{16{state_vs2_q.mode.sigext & vs2_shift_q[16*i + 15]}}, vs2_shift_q[16*i +: 16]};
                    end
                end
                default: ;
            endcase
        end
    end
    always_comb begin
        operand1_d = COMB_INIT_ZERO ? '0 : 'x;
        operand2_d = COMB_INIT_ZERO ? '0 : 'x;
        for (int i = 0; i < ALU_OP_W / 32; i++) begin
            // operand 1 extraction
            operand1_d[36*i+1  +: 8] = state_vs2_q.mode.inv_op1 ? ~operand1[32*i    +: 8] : operand1[32*i    +: 8];
            operand1_d[36*i+10 +: 8] = state_vs2_q.mode.inv_op1 ? ~operand1[32*i+8  +: 8] : operand1[32*i+8  +: 8];
            operand1_d[36*i+19 +: 8] = state_vs2_q.mode.inv_op1 ? ~operand1[32*i+16 +: 8] : operand1[32*i+16 +: 8];
            operand1_d[36*i+28 +: 8] = state_vs2_q.mode.inv_op1 ? ~operand1[32*i+24 +: 8] : operand1[32*i+24 +: 8];
            // operand 2 extraction
            operand2_d[36*i+1  +: 8] = state_vs2_q.mode.inv_op2 ? ~operand2[32*i    +: 8] : operand2[32*i    +: 8];
            operand2_d[36*i+10 +: 8] = state_vs2_q.mode.inv_op2 ? ~operand2[32*i+8  +: 8] : operand2[32*i+8  +: 8];
            operand2_d[36*i+19 +: 8] = state_vs2_q.mode.inv_op2 ? ~operand2[32*i+16 +: 8] : operand2[32*i+16 +: 8];
            operand2_d[36*i+28 +: 8] = state_vs2_q.mode.inv_op2 ? ~operand2[32*i+24 +: 8] : operand2[32*i+24 +: 8];
            // operand 1 carry logic
            operand1_d[36*i   ] =                                 ((state_vs2_q.mode.op_mask == ALU_MASK_CARRY) & operand_mask_d[i*4  ]) ^ state_vs2_q.subtract;
            operand1_d[36*i+9 ] = (state_vs2_q.eew == VSEW_8 ) ? (((state_vs2_q.mode.op_mask == ALU_MASK_CARRY) & operand_mask_d[i*4+1]) ^ state_vs2_q.subtract) : 1'b1;
            operand1_d[36*i+18] = (state_vs2_q.eew != VSEW_32) ? (((state_vs2_q.mode.op_mask == ALU_MASK_CARRY) & operand_mask_d[i*4+2]) ^ state_vs2_q.subtract) : 1'b1;
            operand1_d[36*i+27] = (state_vs2_q.eew == VSEW_8 ) ? (((state_vs2_q.mode.op_mask == ALU_MASK_CARRY) & operand_mask_d[i*4+3]) ^ state_vs2_q.subtract) : 1'b1;
            // operand 2 carry logic
            operand2_d[36*i   ] = 1'b1;
            operand2_d[36*i+9 ] = (state_vs2_q.eew == VSEW_8 ) ? (((state_vs2_q.mode.op_mask == ALU_MASK_CARRY) & operand_mask_d[i*4+1]) ^ state_vs2_q.subtract) : 1'b0;
            operand2_d[36*i+18] = (state_vs2_q.eew != VSEW_32) ? (((state_vs2_q.mode.op_mask == ALU_MASK_CARRY) & operand_mask_d[i*4+2]) ^ state_vs2_q.subtract) : 1'b0;
            operand2_d[36*i+27] = (state_vs2_q.eew == VSEW_8 ) ? (((state_vs2_q.mode.op_mask == ALU_MASK_CARRY) & operand_mask_d[i*4+3]) ^ state_vs2_q.subtract) : 1'b0;
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
    assign result_mask_d = (state_ex2_q.mode.masked ? operand_mask_tmp_q : {(ALU_OP_W/8){1'b1}}) & vl_mask[state_ex2_q.count.val*ALU_OP_W/8 +: ALU_OP_W/8];

    // conversion from results to destination registers:
    logic [ALU_OP_W  -1:0] vd_alu;
    logic [ALU_OP_W/8-1:0] vdmsk_alu;
    vproc_vregpack #(
        .OP_W            ( ALU_OP_W             ),
        .COMB_INIT_ZERO  ( COMB_INIT_ZERO        )
    ) alu_vregpack (
        .vsew_i          ( state_res_q.eew       ),
        .result_i        ( result_alu_q          ),
        .result_narrow_i ( state_res_q.vd_narrow ),
        .result_mask_i   ( result_mask_q         ),
        .vd_o            ( vd_alu                ),
        .vdmsk_o         ( vdmsk_alu             )
    );

    // result shift register assignment:
    store_info vd_info;
    always_comb begin
        vd_info.shift = ~state_res_q.vd_narrow | ~state_res_q.count.val[0];
    end
    `VREGSHIFT_RESULT_NARROW(VREG_W, ALU_OP_W, vd_info, vd_alu, vd_alu_shift_q, vd_alu_shift_d)
    `VREGSHIFT_RESMASK_NARROW(VREG_W, ALU_OP_W, vd_info, vdmsk_alu, vdmsk_alu_shift_q, vdmsk_alu_shift_d)

    // Inactive elements (tail and masked-off elements) are always handled
    // according to the undisturbed policy (i.e., inactive elements are
    // not updated).  However, mask destination values are the only exception,
    // since these can be written at bit granularity and would require a
    // dedicated write enable for each bit, rather than a byte enable.
    // According to the specification mask destination values are always tail-
    // agnostic, hence inactive elements can be left unchanged or overwritten
    // with 1s.  Hence, mask destination values are written after one vector
    // register was processed and all inactive values (according to the mask
    // `result_mask_q') are overwritten with 1s.
    always_comb begin
        vd_cmp_shift_d = COMB_INIT_ZERO ? '0 : 'x;
        vdmsk_cmp_d    = COMB_INIT_ZERO ? '0 : 'x;
        unique case (state_res_q.eew)
            VSEW_8: begin
                vd_cmp_shift_d[VMSK_W  -ALU_OP_W/8 -1:0] = vd_cmp_shift_q[VMSK_W  -1:ALU_OP_W/8 ];
                for (int i = 0; i < ALU_OP_W / 8 ; i++) begin
                    vd_cmp_shift_d[VMSK_W  -ALU_OP_W/8 +i] = result_cmp_q[  i] | ~result_mask_q[i  ];
                end
            end
            VSEW_16: begin
                vd_cmp_shift_d[VMSK_W/2-ALU_OP_W/16-1:0] = vd_cmp_shift_q[VMSK_W/2-1:ALU_OP_W/16];
                for (int i = 0; i < ALU_OP_W / 16; i++) begin
                    vd_cmp_shift_d[VMSK_W/2-ALU_OP_W/16+i] = result_cmp_q[2*i] | ~result_mask_q[2*i];
                end
            end
            VSEW_32: begin
                vd_cmp_shift_d[VMSK_W/4-ALU_OP_W/32-1:0] = vd_cmp_shift_q[VMSK_W/4-1:ALU_OP_W/32];
                if (VMSK_W == 16) begin
                    vd_cmp_shift_d[VMSK_W/2-1:VMSK_W/4] = '1;
                end
                for (int i = 0; i < ALU_OP_W / 32; i++) begin
                    vd_cmp_shift_d[VMSK_W/4-ALU_OP_W/32+i] = result_cmp_q[4*i] | ~result_mask_q[4*i];
                end
            end
            default: ;
        endcase
        unique case (state_res_q.eew)
            VSEW_8:  vdmsk_cmp_d = {{VMSK_W*7 /8 {1'b0}}, {VMSK_W/8 {1'b1}}} << ((VMSK_W/8 ) * state_res_q.count.part.mul);
            VSEW_16: vdmsk_cmp_d = {{VMSK_W*15/16{1'b0}}, {VMSK_W/16{1'b1}}} << ((VMSK_W/16) * state_res_q.count.part.mul);
            VSEW_32: vdmsk_cmp_d = (VMSK_W == 16) ? 16'h0001 << state_res_q.count.part.mul[2:1] :
                                   {{VMSK_W*31/32{1'b0}}, {VMSK_W/32{1'b1}}} << ((VMSK_W/32) * state_res_q.count.part.mul);
            default: ;
        endcase
    end

    //
    assign vreg_wr_en_d   = state_vd_q.busy & state_vd_q.vd_store;
    assign vreg_wr_last_d = state_vd_q.busy & (state_vd_q.mode.cmp ? state_vd_q.last_cycle : state_vd_q.vd_store);
    assign vreg_wr_addr_d = state_vd_q.vd;
    assign vreg_wr_mask_d = vreg_wr_en_o ? (state_vd_q.mode.cmp ? vdmsk_cmp_q : vdmsk_alu_shift_q) : '0;
    assign vreg_wr_d      = state_vd_q.mode.cmp ? {8{vd_cmp_shift_q}} : vd_alu_shift_q;


    ///////////////////////////////////////////////////////////////////////////
    // ALU ARITHMETIC:

    // 37-bit adder (fracturable 32-bit adder with carry-in and carry-out)
    logic [ALU_OP_W*37/32-1:0] sum37;
    always_comb begin
        sum37 = COMB_INIT_ZERO ? '0 : 'x;
        for (int i = 0; i < ALU_OP_W / 32; i++) begin
            sum37[37*i +: 37] = {1'b0, operand2_q[36*i +: 36]} + {1'b0, operand1_q[36*i +: 36]};
        end
    end
    logic [ALU_OP_W/8-1:0] carry, sig_op1, sig_op2, sig_res;
    always_comb begin
        sum_d   = COMB_INIT_ZERO ? '0 : 'x;
        carry   = COMB_INIT_ZERO ? '0 : 'x;
        sig_op1 = COMB_INIT_ZERO ? '0 : 'x;
        sig_op2 = COMB_INIT_ZERO ? '0 : 'x;
        sig_res = COMB_INIT_ZERO ? '0 : 'x;
        for (int i = 0; i < ALU_OP_W / 32; i++) begin
            // discard lowest bit of the 37-bit result and fill in carry chain bits
            sum_d[36*i    +: 8] = sum37[37*i+1  +: 8];
            sum_d[36*i+9  +: 8] = sum37[37*i+10 +: 8];
            sum_d[36*i+18 +: 8] = sum37[37*i+19 +: 8];
            sum_d[36*i+27 +: 8] = sum37[37*i+28 +: 8];
            unique case (state_ex1_q.eew)
                VSEW_8: begin
                    sum_d  [36*i+8   ] =  sum37     [37*i+9 ] ^ state_ex1_q.subtract;
                    sum_d  [36*i+17  ] =  sum37     [37*i+18] ^ state_ex1_q.subtract;
                    sum_d  [36*i+26  ] =  sum37     [37*i+27] ^ state_ex1_q.subtract;
                    sum_d  [36*i+35  ] =  sum37     [37*i+36] ^ state_ex1_q.subtract;
                    carry  [4 *i +: 4] = {sum37     [37*i+36], sum37     [37*i+27], sum37     [37*i+18], sum37     [37*i+9]};
                    sig_op1[4 *i +: 4] = {operand1_q[36*i+35], operand1_q[36*i+26], operand1_q[36*i+17], operand1_q[36*i+8]};
                    sig_op2[4 *i +: 4] = {operand2_q[36*i+35], operand2_q[36*i+26], operand2_q[36*i+17], operand2_q[36*i+8]};
                    sig_res[4 *i +: 4] = {sum37     [37*i+35], sum37     [37*i+26], sum37     [37*i+17], sum37     [37*i+8]};
                end
                VSEW_16: begin
                    sum_d  [36*i+8   ] =     sum37     [37*i+10];
                    sum_d  [36*i+17  ] =     sum37     [37*i+18] ^ state_ex1_q.subtract;
                    sum_d  [36*i+26  ] =     sum37     [37*i+28];
                    sum_d  [36*i+35  ] =     sum37     [37*i+36] ^ state_ex1_q.subtract;
                    carry  [4 *i +: 4] = {{2{sum37     [37*i+36]}}, {2{sum37     [37*i+18]}}};
                    sig_op1[4 *i +: 4] = {{2{operand1_q[36*i+35]}}, {2{operand1_q[36*i+17]}}};
                    sig_op2[4 *i +: 4] = {{2{operand2_q[36*i+35]}}, {2{operand2_q[36*i+17]}}};
                    sig_res[4 *i +: 4] = {{2{sum37     [37*i+35]}}, {2{sum37     [37*i+17]}}};
                end
                VSEW_32: begin
                    sum_d  [36*i+8   ] =    sum37     [37*i+10];
                    sum_d  [36*i+17  ] =    sum37     [37*i+19];
                    sum_d  [36*i+26  ] =    sum37     [37*i+28];
                    sum_d  [36*i+35  ] =    sum37     [37*i+36] ^ state_ex1_q.subtract;
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
        cmp_d = COMB_INIT_ZERO ? '0 : 'x;
        unique case (state_ex1_q.mode.opx1.sel)
            ALU_SEL_CARRY: cmp_d = state_ex1_q.subtract ? ~carry : carry;
            ALU_SEL_OVFLW: cmp_d = ovflw;
            ALU_SEL_LT:    cmp_d = ovflw ^ sig_res; // minuend is less than subtrahend
            ALU_SEL_MASK: begin
                for (int i = 0; i < ALU_OP_W / 8; i++) begin
                    cmp_d[i] = (state_ex1_q.mode.op_mask == ALU_MASK_SEL) & operand_mask_q[i];
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
        mode_signed = COMB_INIT_ZERO ? '0 : 'x;
        unique case (state_ex1_q.mode.opx1.sel)
            ALU_SEL_CARRY: mode_signed = 1'b0;
            ALU_SEL_OVFLW: mode_signed = 1'b1;
            default: ;
        endcase
    end
    always_comb begin
        satval_d = COMB_INIT_ZERO ? '0 : 'x;
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
    always_comb begin
        shift_res_d = COMB_INIT_ZERO ? '0 : 'x;
        unique case ({state_ex1_q.mode.opx1.shift, state_ex1_q.eew})
            // vsll.*
            {ALU_SHIFT_VSLL, VSEW_8}: begin
                for (int i = 0; i < ALU_OP_W / 8 ; i++)
                    shift_res_d[8 *i +: 8 ] = operand2_32[8 *i +: 8 ] << operand1_32[8 *i +: 3];
            end
            {ALU_SHIFT_VSLL, VSEW_16}: begin
                for (int i = 0; i < ALU_OP_W / 16; i++)
                    shift_res_d[16*i +: 16] = operand2_32[16*i +: 16] << operand1_32[16*i +: 4];
            end
            {ALU_SHIFT_VSLL, VSEW_32}: begin
                for (int i = 0; i < ALU_OP_W / 32; i++)
                    shift_res_d[32*i +: 32] = operand2_32[32*i +: 32] << operand1_32[32*i +: 5];
            end

            // vsrl.*
            {ALU_SHIFT_VSRL, VSEW_8}: begin
                for (int i = 0; i < ALU_OP_W / 8 ; i++)
                    shift_res_d[8 *i +: 8 ] = operand2_32[8 *i +: 8 ] >> operand1_32[8 *i +: 3];
            end
            {ALU_SHIFT_VSRL, VSEW_16}: begin
                for (int i = 0; i < ALU_OP_W / 16; i++)
                    shift_res_d[16*i +: 16] = operand2_32[16*i +: 16] >> operand1_32[16*i +: 4];
            end
            {ALU_SHIFT_VSRL, VSEW_32}: begin
                for (int i = 0; i < ALU_OP_W / 32; i++)
                    shift_res_d[32*i +: 32] = operand2_32[32*i +: 32] >> operand1_32[32*i +: 5];
            end

            // vsra.*
            {ALU_SHIFT_VSRA, VSEW_8}: begin
                for (int i = 0; i < ALU_OP_W / 8 ; i++)
                    shift_res_d[8 *i +: 8 ] = $signed(operand2_32[8 *i +: 8 ]) >>> operand1_32[8 *i +: 3];
            end
            {ALU_SHIFT_VSRA, VSEW_16}: begin
                for (int i = 0; i < ALU_OP_W / 16; i++)
                    shift_res_d[16*i +: 16] = $signed(operand2_32[16*i +: 16]) >>> operand1_32[16*i +: 4];
            end
            {ALU_SHIFT_VSRA, VSEW_32}: begin
                for (int i = 0; i < ALU_OP_W / 32; i++)
                    shift_res_d[32*i +: 32] = $signed(operand2_32[32*i +: 32]) >>> operand1_32[32*i +: 5];
            end
            default: ;
        endcase
    end

    // arithmetic result
    always_comb begin
        result_alu_d = COMB_INIT_ZERO ? '0 : 'x;
        unique case (state_ex2_q.mode.opx2.res)
            // add and saturating add: the result is replaced by the saturation
            // value if the corresponding bit in the compare register is set;
            // for non-saturating addition (and subtraction) the compare
            // register has to be 0
            ALU_VADD: begin
                for (int i = 0; i < ALU_OP_W / 8; i++) begin
                    result_alu_d[8*i +: 8] = cmp_q[i] ? {satval_q[2*i+1], {7{satval_q[2*i]}}} : sum_q[9*i +: 8];
                end
            end

            // averaging add: the result is right-shifted by one bit (the carry
            // in of the addition can be used to control rounding behavior)
            ALU_VAADD: begin
                for (int i = 0; i < ALU_OP_W / 8; i++) begin
                    result_alu_d[8*i +: 8] = sum_q[9*i+1 +: 8];
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
        neq = COMB_INIT_ZERO ? '0 : 'x;
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
        result_cmp_d = COMB_INIT_ZERO ? '0 : 'x;
        unique case (state_ex2_q.mode.opx2.cmp)
            ALU_CMP_CMP:  result_cmp_d =  cmp_q;
            ALU_CMP_CMPN: result_cmp_d = ~cmp_q;
            ALU_CMP_EQ:   result_cmp_d = ~neq;
            ALU_CMP_NE:   result_cmp_d =  neq;
            default: ;
        endcase
    end

endmodule
