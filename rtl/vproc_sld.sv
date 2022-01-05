// Copyright TU Wien
// Licensed under the ISC license, see LICENSE.txt for details
// SPDX-License-Identifier: ISC


module vproc_sld #(
        parameter int unsigned        VREG_W          = 128,  // width in bits of vector registers
        parameter int unsigned        VMSK_W          = 16,   // width of vector register masks (= VREG_W / 8)
        parameter int unsigned        CFG_VL_W        = 7,    // width of VL reg in bits (= log2(VREG_W))
        parameter int unsigned        SLD_OP_W        = 64,   // SLD unit operand width in bits
        parameter int unsigned        MAX_WR_ATTEMPTS = 1,    // max required vregfile write attempts
        parameter bit                 BUF_VREG        = 1'b1, // insert pipeline stage after vreg read
        parameter bit                 BUF_OPERANDS    = 1'b1, // insert pipeline stage after operand extraction
        parameter bit                 BUF_RESULTS     = 1'b1, // insert pipeline stage after computing result
        parameter bit                 DONT_CARE_ZERO  = 1'b0  // initialize don't care values to zero
    )(
        input  logic                  clk_i,
        input  logic                  async_rst_ni,
        input  logic                  sync_rst_ni,

        input  vproc_pkg::cfg_vsew    vsew_i,
        input  vproc_pkg::cfg_lmul    lmul_i,
        input  logic [CFG_VL_W-1:0]   vl_i,
        input  logic                  vl_0_i,

        input  logic                  op_rdy_i,
        output logic                  op_ack_o,

        input  vproc_pkg::op_mode_sld mode_i,
        input  logic [31:0]           rs1_i,
        input  logic [4:0]            vs2_i,
        input  logic [4:0]            vd_i,

        output logic [31:0]           clear_rd_hazards_o,
        output logic [31:0]           clear_wr_hazards_o,

        // connections to register file:
        input  logic [VREG_W-1:0]     vreg_mask_i,
        input  logic [VREG_W-1:0]     vreg_rd_i,
        output logic [4:0]            vreg_rd_addr_o,
        output logic [VREG_W-1:0]     vreg_wr_o,
        output logic [4:0]            vreg_wr_addr_o,
        output logic [VMSK_W-1:0]     vreg_wr_mask_o,
        output logic                  vreg_wr_en_o
    );

    import vproc_pkg::*;

    if ((SLD_OP_W & (SLD_OP_W - 1)) != 0 || SLD_OP_W < 32 || SLD_OP_W >= VREG_W) begin
        $fatal(1, "The vector SLD operand width SLD_OP_W must be at least 32, less than ",
                  "the vector register width VREG_W and a power of two.  ",
                  "The current value of %d is invalid.", SLD_OP_W);
    end

    if (MAX_WR_ATTEMPTS < 1 || (1 << (MAX_WR_ATTEMPTS - 1)) > VREG_W / SLD_OP_W) begin
        $fatal(1, "The maximum number of write attempts MAX_WR_ATTEMPTS of a unit ",
                  "must be at least 1 and 2^(MAX_WR_ATTEMPTS-1) must be less than or ",
                  "equal to the ratio of the vector register width vs the operand width ",
                  "of that unit.  ",
                  "For the vector SLD unit MAX_WR_ATTEMPTS is %d and that ratio is %d.",
                  MAX_WR_ATTEMPTS, VREG_W / SLD_OP_W);
    end

    // max number of cycles by which a write can be delayed
    localparam int unsigned MAX_WR_DELAY = (1 << (MAX_WR_ATTEMPTS - 1)) - 1;


    ///////////////////////////////////////////////////////////////////////////
    // SLD UNIT STATE:

    localparam int unsigned SLD_CYCLES_PER_VREG = VREG_W / SLD_OP_W;
    localparam int unsigned SLD_COUNTER_W       = $clog2(SLD_CYCLES_PER_VREG) + 4;

    localparam int unsigned SLD_OP_SHFT_W = $clog2(SLD_OP_W / 8);

    localparam int unsigned RESMSK_W = SLD_OP_W / 8; // size of result masks

    // note that in contrast to other units the mul part of the counter is 4 bits
    typedef union packed {
        logic [SLD_COUNTER_W-1:0] val;
        struct packed {
            logic [3:0]               mul; // mul part (vreg index)
            logic [SLD_COUNTER_W-5:0] low; // counter part in vreg (vreg pos)
        } part;
    } sld_counter;

    typedef struct packed {
        sld_counter               count;
        sld_counter               count_store;
        logic [SLD_OP_SHFT_W-1:0] op_shift;
        logic                     first_cycle;
        logic                     last_cycle;
        op_mode_sld               mode;
        cfg_vsew                  eew;        // effective element width
        cfg_emul                  emul;       // effective MUL factor
        logic [CFG_VL_W-1:0]      vl;
        logic                     vl_0;
        logic [31:0]              rs1;
        logic [4:0]               vs2;
        logic                     vs2_fetch;
        logic [4:0]               vd_base;
        logic [4:0]               vd;
        logic                     vd_store;
    } sld_state;

    logic     state_valid_q,  state_valid_d;
    sld_state state_q,        state_d;
    always_ff @(posedge clk_i or negedge async_rst_ni) begin : vproc_sld_state_valid
        if (~async_rst_ni) begin
            state_valid_q <= 1'b0;
        end
        else if (~sync_rst_ni) begin
            state_valid_q <= 1'b0;
        end else begin
            state_valid_q <= state_valid_d;
        end
    end
    always_ff @(posedge clk_i) begin : vproc_sld_state
        state_q <= state_d;
    end

    // in contrast to other units the last cycle is delayed by the cycles required for one VREG
    logic last_cycle;
    always_comb begin
        last_cycle = DONT_CARE_ZERO ? 1'b0 : 1'bx;
        unique case (state_q.emul)
            EMUL_1: last_cycle = state_q.count.part.mul[0] & (state_q.count.part.low == '1);
            EMUL_2: last_cycle = state_q.count.part.mul[1] & (state_q.count.part.low == '1);
            EMUL_4: last_cycle = state_q.count.part.mul[2] & (state_q.count.part.low == '1);
            EMUL_8: last_cycle = state_q.count.part.mul[3] & (state_q.count.part.low == '1);
            default: ;
        endcase
    end

    logic [$clog2(VREG_W)-1:0] byte_slide; // slide amount in bytes
    logic                      sld_valid;  // slide amount is valid for LMUL == 8 (i.e. no overflow)
    always_comb begin
        byte_slide = DONT_CARE_ZERO ?   '0 :   'x;
        sld_valid  = DONT_CARE_ZERO ? 1'b0 : 1'bx;
        unique case (mode_i.op)
            SLD_UP, SLD_DOWN: begin
                unique case (vsew_i)
                    VSEW_8: begin
                        byte_slide =  rs1_i[$clog2(VREG_W)-1:0];
                        sld_valid  =  rs1_i[31:$clog2(VREG_W)] == '0;
                    end
                    VSEW_16: begin
                        byte_slide = {rs1_i[$clog2(VREG_W)-2:0], 1'b0};
                        sld_valid  =  rs1_i[31:$clog2(VREG_W)-1] == '0;
                    end
                    VSEW_32: begin
                        byte_slide = {rs1_i[$clog2(VREG_W)-3:0], 2'b00};
                        sld_valid  =  rs1_i[31:$clog2(VREG_W)-2] == '0;
                    end
                    default: ;
                endcase
            end
            SLD_1UP, SLD_1DOWN: begin
                unique case (vsew_i)
                    VSEW_8:  byte_slide = 1;
                    VSEW_16: byte_slide = 2;
                    VSEW_32: byte_slide = 4;
                    default: ;
                endcase
                sld_valid = 1'b1;
            end
            default: ;
        endcase
    end

    logic pipeline_ready;
    always_comb begin
        op_ack_o       = 1'b0;
        state_valid_d  = state_valid_q;
        state_d        = state_q;

        if (((~state_valid_q) | (last_cycle & pipeline_ready)) & op_rdy_i) begin
            op_ack_o            = 1'b1;
            state_d.count.val   = '0;
            state_valid_d       = 1'b1;
            state_d.first_cycle = 1'b1;
            state_d.mode        = mode_i;
            state_d.eew         = vsew_i;
            state_d.emul = DONT_CARE_ZERO ? cfg_emul'('0) : cfg_emul'('x);
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
            state_d.vl          = vl_i;
            state_d.vl_0        = vl_0_i;
            state_d.rs1         = rs1_i;
            state_d.vs2         = vs2_i;
            state_d.vs2_fetch   = 1'b1;
            state_d.vd_base     = vd_i;
            state_d.vd          = vd_i;
            unique case (mode_i.op)
                SLD_UP, SLD_1UP: begin
                    state_d.count_store.val = {1'b0,  byte_slide[$clog2(VREG_W)-1:SLD_OP_SHFT_W]} - ((byte_slide[SLD_OP_SHFT_W-1:0] == '0) ? 1 : 0);
                    state_d.op_shift        = -byte_slide[SLD_OP_SHFT_W-1:0];
                end
                SLD_DOWN, SLD_1DOWN: begin
                    state_d.count_store.val = {1'b1, ~byte_slide[$clog2(VREG_W)-1:SLD_OP_SHFT_W]};
                    state_d.op_shift        =  byte_slide[SLD_OP_SHFT_W-1:0];
                end
                default: ;
            endcase
            if (~sld_valid) begin
                state_d.count_store.val = {1'b1, {(SLD_COUNTER_W-1){1'b0}}};
                state_d.op_shift        = '0;
            end
        end
        else if (state_valid_q & pipeline_ready) begin
            state_d.count.val       = state_q.count.val + 1;
            state_d.count_store.val = state_q.count_store.val + 1;
            state_valid_d           = ~last_cycle;
            state_d.first_cycle     = 1'b0;
            state_d.vs2_fetch       = 1'b0;
            if (state_q.count.part.low == '1) begin
                state_d.vs2[2:0]  = state_q.vs2[2:0] + 3'b1;
                state_d.vs2_fetch = 1'b1;
            end
        end
    end


    ///////////////////////////////////////////////////////////////////////////
    // SLD PIPELINE BUFFERS:

    // pass state information along pipeline:
    logic                       state_vreg_ready,   state_vs_ready,   state_ex_ready,   state_res_ready,   state_vd_ready;
    logic     state_init_valid, state_vreg_valid_q, state_vs_valid_q, state_ex_valid_q, state_res_valid_q, state_vd_valid_q;
    sld_state state_init,       state_vreg_q,       state_vs_q,       state_ex_q,       state_res_q,       state_vd_q;
    always_comb begin
        state_init_valid      = state_valid_q;
        state_init            = state_q;
        state_init.last_cycle = state_valid_q & last_cycle;
        state_init.vd_store   = (state_q.count_store.part.low == '1) & ~state_q.count_store.part.mul[3];
        //state_init.vd[2:0]    = state_q.vd[2:0] | state_q.count_store.part.mul[2:0];
    end
    assign pipeline_ready = state_vreg_ready;

    // vreg read register:
    logic [VREG_W-1:0] vreg_rd_q, vreg_rd_d;

    // operand shift register:
    logic [VREG_W-1:0]   vs2_shift_q,  vs2_shift_d;
    logic [SLD_OP_W-1:0] vs2_tmp_q,    vs2_tmp_d;
    logic [VREG_W-1:0]   v0msk_q,      v0msk_d;
    logic [VMSK_W-1:0]   v0msk_part_q, v0msk_part_d;

    // operands and result:
    logic [SLD_OP_W-1:0] operand_low_q,  operand_low_d;
    logic [SLD_OP_W-1:0] operand_high_q, operand_high_d;
    logic [SLD_OP_W-1:0] result_q,       result_d;
    logic [RESMSK_W-1:0] result_mask_q,  result_mask_d;
    logic [VMSK_W  -1:0] write_mask_q,   write_mask_d;

    // result shift register:
    logic [VREG_W-1:0] vd_shift_q,     vd_shift_d;
    logic [VMSK_W-1:0] vdmsk_shift_q,  vdmsk_shift_d;
    logic [VMSK_W-1:0] vdmsk_static_q, vdmsk_static_d;

    // vreg write buffers
    localparam WRITE_BUFFER_SZ = (MAX_WR_DELAY > 0) ? MAX_WR_DELAY : 1;
    logic              vreg_wr_en_q   [WRITE_BUFFER_SZ], vreg_wr_en_d;
    logic [4:0]        vreg_wr_addr_q [WRITE_BUFFER_SZ], vreg_wr_addr_d;
    logic [VMSK_W-1:0] vreg_wr_mask_q [WRITE_BUFFER_SZ], vreg_wr_mask_d;
    logic [VREG_W-1:0] vreg_wr_q      [WRITE_BUFFER_SZ], vreg_wr_d;
    logic              vreg_wr_clear_q[WRITE_BUFFER_SZ], vreg_wr_clear_d;
    logic [4:0]        vreg_wr_base_q [WRITE_BUFFER_SZ], vreg_wr_base_d;
    cfg_emul           vreg_wr_emul_q [WRITE_BUFFER_SZ], vreg_wr_emul_d;

    // hazard clear registers
    logic [31:0] clear_rd_hazards_q, clear_rd_hazards_d;
    logic [31:0] clear_wr_hazards_q, clear_wr_hazards_d;

    generate
        if (BUF_VREG) begin
            always_ff @(posedge clk_i or negedge async_rst_ni) begin : vproc_sld_stage_vreg_valid
                if (~async_rst_ni) begin
                    state_vreg_valid_q <= 1'b0;
                end
                else if (~sync_rst_ni) begin
                    state_vreg_valid_q <= 1'b0;
                end
                else if (state_vreg_ready) begin
                    state_vreg_valid_q <= state_init_valid;
                end
            end
            always_ff @(posedge clk_i) begin : vproc_sld_stage_vreg
                if (state_vreg_ready & state_init_valid) begin
                    state_vreg_q <= state_init;
                    vreg_rd_q    <= vreg_rd_d;
                end
            end
            assign state_vreg_ready = ~state_vreg_valid_q | state_vs_ready;
        end else begin
            always_comb begin
                state_vreg_valid_q = state_init_valid;
                state_vreg_q       = state_init;
                vreg_rd_q          = vreg_rd_d;
            end
            assign state_vreg_ready = state_vs_ready;
        end

        always_ff @(posedge clk_i or negedge async_rst_ni) begin : vproc_sld_stage_vs_valid
            if (~async_rst_ni) begin
                state_vs_valid_q <= 1'b0;
            end
            else if (~sync_rst_ni) begin
                state_vs_valid_q <= 1'b0;
            end
            else if (state_vs_ready) begin
                state_vs_valid_q <= state_vreg_valid_q;
            end
        end
        always_ff @(posedge clk_i) begin : vproc_sld_stage_vs
            if (state_vs_ready & state_vreg_valid_q) begin
                state_vs_q  <= state_vreg_q;
                vs2_shift_q <= vs2_shift_d;
                vs2_tmp_q   <= vs2_tmp_d;
                v0msk_q     <= v0msk_d;
            end
        end
        assign state_vs_ready = ~state_vs_valid_q | state_ex_ready;

        if (BUF_OPERANDS) begin
            always_ff @(posedge clk_i or negedge async_rst_ni) begin : vproc_sld_stage_ex_valid
                if (~async_rst_ni) begin
                    state_ex_valid_q <= 1'b0;
                end
                else if (~sync_rst_ni) begin
                    state_ex_valid_q <= 1'b0;
                end
                else if (state_ex_ready) begin
                    state_ex_valid_q <= state_vs_valid_q;
                end
            end
            always_ff @(posedge clk_i) begin : vproc_sld_stage_ex
                if (state_ex_ready & state_vs_valid_q) begin
                    state_ex_q     <= state_vs_q;
                    operand_low_q  <= operand_low_d;
                    operand_high_q <= operand_high_d;
                    v0msk_part_q   <= v0msk_part_d;
                end
            end
            assign state_ex_ready = ~state_ex_valid_q | state_res_ready;
        end else begin
            always_comb begin
                state_ex_valid_q = state_vs_valid_q;
                state_ex_q       = state_vs_q;
                operand_low_q    = operand_low_d;
                operand_high_q   = operand_high_d;
                v0msk_part_q     = v0msk_part_d;
            end
            assign state_ex_ready = state_res_ready;
        end

        if (BUF_RESULTS) begin
            always_ff @(posedge clk_i or negedge async_rst_ni) begin : vproc_sld_stage_res_valid
                if (~async_rst_ni) begin
                    state_res_valid_q <= 1'b0;
                end
                else if (~sync_rst_ni) begin
                    state_res_valid_q <= 1'b0;
                end
                else if (state_res_ready) begin
                    state_res_valid_q <= state_ex_valid_q;
                end
            end
            always_ff @(posedge clk_i) begin : vproc_sld_stage_res
                if (state_res_ready & state_ex_valid_q) begin
                    state_res_q   <= state_ex_q;
                    result_q      <= result_d;
                    result_mask_q <= result_mask_d;
                    write_mask_q  <= write_mask_d;
                end
            end
            assign state_res_ready = ~state_res_valid_q | state_vd_ready;
        end else begin
            always_comb begin
                state_res_valid_q = state_ex_valid_q;
                state_res_q       = state_ex_q;
                result_q          = result_d;
                result_mask_q     = result_mask_d;
                write_mask_q      = write_mask_d;
            end
            assign state_res_ready = state_vd_ready;
        end

        always_ff @(posedge clk_i or negedge async_rst_ni) begin : vproc_sld_stage_vd_valid
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
        always_ff @(posedge clk_i) begin : vproc_sld_stage_vd
            if (state_vd_ready & state_res_valid_q) begin
                state_vd_q     <= state_res_q;
                vd_shift_q     <= vd_shift_d;
                vdmsk_shift_q  <= vdmsk_shift_d;
                vdmsk_static_q <= vdmsk_static_d;
            end
        end
        assign state_vd_ready = ~state_vd_valid_q | 1'b1;

        if (MAX_WR_DELAY > 0) begin
            always_ff @(posedge clk_i) begin : vproc_sld_wr_delay
                vreg_wr_en_q   [0] <= vreg_wr_en_d;
                vreg_wr_addr_q [0] <= vreg_wr_addr_d;
                vreg_wr_mask_q [0] <= vreg_wr_mask_d;
                vreg_wr_q      [0] <= vreg_wr_d;
                vreg_wr_clear_q[0] <= vreg_wr_clear_d;
                vreg_wr_base_q [0] <= vreg_wr_base_d;
                vreg_wr_emul_q [0] <= vreg_wr_emul_d;
                for (int i = 1; i < MAX_WR_DELAY; i++) begin
                    vreg_wr_en_q   [i] <= vreg_wr_en_q   [i-1];
                    vreg_wr_addr_q [i] <= vreg_wr_addr_q [i-1];
                    vreg_wr_mask_q [i] <= vreg_wr_mask_q [i-1];
                    vreg_wr_q      [i] <= vreg_wr_q      [i-1];
                    vreg_wr_clear_q[i] <= vreg_wr_clear_q[i-1];
                    vreg_wr_base_q [i] <= vreg_wr_base_q [i-1];
                    vreg_wr_emul_q [i] <= vreg_wr_emul_q [i-1];
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
        if (MAX_WR_DELAY == 0) begin
            clear_wr_hazards_d = DONT_CARE_ZERO ? '0 : 'x;
            unique case (vreg_wr_emul_d)
                EMUL_1: clear_wr_hazards_d = 32'h00000001 << {vreg_wr_base_d                           };
                EMUL_2: clear_wr_hazards_d = 32'h00000003 << {vreg_wr_base_d                [4:1], 1'b0};
                EMUL_4: clear_wr_hazards_d = 32'h0000000F << {vreg_wr_base_d                [4:2], 2'b0};
                EMUL_8: clear_wr_hazards_d = 32'h000000FF << {vreg_wr_base_d                [4:3], 3'b0};
                default: ;
            endcase
            if (~vreg_wr_clear_d) begin
                clear_wr_hazards_d = '0;
            end
        end else begin
            unique case (vreg_wr_emul_q[MAX_WR_DELAY-1])
                EMUL_1: clear_wr_hazards_d = 32'h00000001 << {vreg_wr_base_q[MAX_WR_DELAY-1]           };
                EMUL_2: clear_wr_hazards_d = 32'h00000003 << {vreg_wr_base_q[MAX_WR_DELAY-1][4:1], 1'b0};
                EMUL_4: clear_wr_hazards_d = 32'h0000000F << {vreg_wr_base_q[MAX_WR_DELAY-1][4:2], 2'b0};
                EMUL_8: clear_wr_hazards_d = 32'h000000FF << {vreg_wr_base_q[MAX_WR_DELAY-1][4:3], 3'b0};
                default: ;
            endcase
            if (~vreg_wr_clear_q[MAX_WR_DELAY-1]) begin
                clear_wr_hazards_d = '0;
            end
        end
    end
    assign clear_wr_hazards_o = clear_wr_hazards_q;

    // read hazard clearing
    assign clear_rd_hazards_d = state_init_valid ? (
        ((state_init.vs2_fetch & ~state_init.last_cycle) ? (32'b1 << state_init.vs2) : 32'b0) |
        {31'b0, state_init.mode.masked & state_init.first_cycle}
    ) : 32'b0;
    assign clear_rd_hazards_o = clear_rd_hazards_q;


    ///////////////////////////////////////////////////////////////////////////
    // SLD REGISTER READ/WRITE:

    // source register addressing and read:
    assign vreg_rd_addr_o = state_init.vs2;
    assign vreg_rd_d      = vreg_rd_i;

    // operand shift register assignment:
    always_comb begin
        vs2_shift_d = vreg_rd_q;
        v0msk_d     = vreg_mask_i;
        if (~state_vreg_q.vs2_fetch) begin
            vs2_shift_d[VREG_W-SLD_OP_W-1:0] = vs2_shift_q[VREG_W-1:SLD_OP_W];
        end
        if (~state_vreg_q.first_cycle) begin
            v0msk_d = v0msk_q;
        end
    end

    // spill source shift register into temporary buffer, extract relevant part of mask register
    assign vs2_tmp_d    = vs2_shift_q[SLD_OP_W-1:0];
    assign v0msk_part_d = v0msk_q[state_vs_q.count_store.part.mul[2:0]*VMSK_W +: VMSK_W];

    // extract operands, substitute with rs1 when invalid to accomodate 1up and 1down operations
    logic [SLD_COUNTER_W-1:0] vl_cnt;
    assign vl_cnt = {1'b0, state_vs_q.vl[CFG_VL_W-1:CFG_VL_W-SLD_COUNTER_W+1]} + 1;
    always_comb begin
        operand_low_d  = vs2_tmp_q;
        operand_high_d = vs2_shift_q[SLD_OP_W-1:0];
        if (state_vs_q.first_cycle) begin
            unique case (state_vs_q.eew)
                VSEW_8:  operand_low_d[SLD_OP_W-1:SLD_OP_W-8 ] = state_vs_q.rs1[7 :0];
                VSEW_16: operand_low_d[SLD_OP_W-1:SLD_OP_W-16] = state_vs_q.rs1[15:0];
                VSEW_32: operand_low_d[SLD_OP_W-1:SLD_OP_W-32] = state_vs_q.rs1      ;
                default: ;
            endcase
        end
        if ((state_vs_q.mode.op == SLD_1UP) | (state_vs_q.mode.op == SLD_1DOWN)) begin
            if (state_vs_q.count.val == vl_cnt) begin
                // TODO move this to the appropriate position depending on VL
                operand_high_d[31:0] = state_vs_q.rs1;
            end
        end else begin
            // for vslidedown the source elements beyond VLMAX are 0
            if (state_vs_q.count.part.mul >= (4'b0001 << state_vs_q.emul)) begin
                operand_high_d = '0;
            end
        end
    end

    // convert element mask to byte mask
    always_comb begin
        write_mask_d = DONT_CARE_ZERO ? '0 : 'x;
        unique case (state_ex_q.eew)
            VSEW_8: begin
                write_mask_d = v0msk_part_q;
            end
            VSEW_16: begin
                for (int i = 0; i < VREG_W / 16; i++) begin
                    write_mask_d[i*2  ] = v0msk_part_q[i];
                    write_mask_d[i*2+1] = v0msk_part_q[i];
                end
            end
            VSEW_32: begin
                for (int i = 0; i < VREG_W / 32; i++) begin
                    write_mask_d[i*4  ] = v0msk_part_q[i];
                    write_mask_d[i*4+1] = v0msk_part_q[i];
                    write_mask_d[i*4+2] = v0msk_part_q[i];
                    write_mask_d[i*4+3] = v0msk_part_q[i];
                end
            end
            default: ;
        endcase
    end

    logic [VREG_W    -1:0] vl_mask;
    logic [SLD_OP_W/8-1:0] result_vl_mask;
    assign vl_mask        = state_res_q.vl_0 ? {VREG_W{1'b0}} : ({VREG_W{1'b1}} >> (~state_res_q.vl));
    assign result_vl_mask = vl_mask[state_res_q.count_store.val[SLD_COUNTER_W-2:0]*SLD_OP_W/8 +: SLD_OP_W/8];

    // result shift register assignment:
    assign vd_shift_d    = {result_q, vd_shift_q[VREG_W-1:SLD_OP_W]};
    assign vdmsk_shift_d = {result_mask_q & result_vl_mask,
                            state_res_q.first_cycle ? {VMSK_W-RESMSK_W{1'b0}} : vdmsk_shift_q[VMSK_W-1:RESMSK_W]};

    // static write mask:
    assign vdmsk_static_d = state_res_q.mode.masked ? write_mask_q : {VMSK_W{1'b1}};

    //
    assign vreg_wr_en_d    = state_vd_valid_q & state_vd_q.vd_store;
    // TODO after finding a better way to clear hazards, simplify the addressing logic
    assign vreg_wr_addr_d  = state_vd_q.vd | {2'b0, state_vd_q.count_store.part.mul[2:0]};
    assign vreg_wr_mask_d  = vreg_wr_en_o ? (vdmsk_shift_q & vdmsk_static_q) : '0;
    assign vreg_wr_d       = vd_shift_q;
    assign vreg_wr_clear_d = state_vd_valid_q & state_vd_q.last_cycle;
    assign vreg_wr_base_d  = state_vd_q.vd_base;
    assign vreg_wr_emul_d  = state_vd_q.emul;


    ///////////////////////////////////////////////////////////////////////////
    // SLIDING OPERATION:

    // operand valid flags (low operand is invalid in first cycle, high operand is invalid in last cycle)
    logic op_low_valid, op_high_valid;
    assign op_low_valid  = ~state_ex_q.first_cycle;
    assign op_high_valid = ~state_ex_q.last_cycle;

    always_comb begin
        result_d      = DONT_CARE_ZERO ? '0 : 'x;
        result_mask_d = DONT_CARE_ZERO ? '0 : 'x;

        for (int i = 0; i < SLD_OP_W/8; i++) begin
            if ({3'b000, state_ex_q.op_shift} + $clog2(SLD_OP_W)'(i) < $clog2(SLD_OP_W)'(SLD_OP_W/8)) begin
                result_d     [i*8 +: 8] = operand_low_q [({3'b000, state_ex_q.op_shift} + $clog2(SLD_OP_W)'(i)                                ) * 8 +: 8];
                result_mask_d[i]        = op_low_valid;
            end else begin
                result_d     [i*8 +: 8] = operand_high_q[({3'b000, state_ex_q.op_shift} + $clog2(SLD_OP_W)'(i) - $clog2(SLD_OP_W)'(SLD_OP_W/8)) * 8 +: 8];
                result_mask_d[i]        = op_high_valid;
            end
        end

        if ((state_ex_q.mode.op == SLD_1UP) | (state_ex_q.mode.op == SLD_1DOWN)) begin
            result_mask_d = {RESMSK_W{1'b1}};
        end
    end

endmodule

