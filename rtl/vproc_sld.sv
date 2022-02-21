// Copyright TU Wien
// Licensed under the Solderpad Hardware License v2.1, see LICENSE.txt for details
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1


module vproc_sld #(
        parameter int unsigned        VREG_W         = 128,  // width in bits of vector registers
        parameter int unsigned        CFG_VL_W       = 7,    // width of VL reg in bits (= log2(VREG_W))
        parameter int unsigned        SLD_OP_W       = 64,   // SLD unit operand width in bits
        parameter bit                 BUF_OPERANDS   = 1'b1, // insert pipeline stage after operand extraction
        parameter bit                 BUF_RESULTS    = 1'b1, // insert pipeline stage after computing result
        parameter type                CTRL_T         = logic,
        parameter bit                 DONT_CARE_ZERO = 1'b0  // initialize don't care values to zero
    )(
        input  logic                  clk_i,
        input  logic                  async_rst_ni,
        input  logic                  sync_rst_ni,

        input  logic                  pipe_in_valid_i,
        output logic                  pipe_in_ready_o,
        input  CTRL_T                 pipe_in_ctrl_i,
        input  logic [SLD_OP_W  -1:0] pipe_in_op_i,
        input  logic [SLD_OP_W/8-1:0] pipe_in_mask_i,

        output logic                  pipe_out_valid_o,
        input  logic                  pipe_out_ready_i,
        output CTRL_T                 pipe_out_ctrl_o,
        output logic [SLD_OP_W  -1:0] pipe_out_res_o,
        output logic [SLD_OP_W/8-1:0] pipe_out_mask_o
    );

    import vproc_pkg::*;


    ///////////////////////////////////////////////////////////////////////////
    // SLD BUFFERS

    logic  state_ex_ready,                     state_res_ready;
    logic  state_ex_valid_q, state_ex_valid_d, state_res_valid_q;
    CTRL_T state_ex_q,       state_ex_d,       state_res_q;

    // operands and result:
    logic [SLD_OP_W/8-1:0] v0msk_q,        v0msk_d;
    logic                  operand_low_valid_q, operand_low_valid_d;
    logic [SLD_OP_W  -1:0] operand_low_q,  operand_low_d;
    logic [SLD_OP_W  -1:0] operand_high_q, operand_high_d;
    logic [SLD_OP_W  -1:0] result_q,       result_d;
    logic [SLD_OP_W/8-1:0] result_mask_q,  result_mask_d;
    logic [SLD_OP_W/8-1:0] write_mask_q,   write_mask_d;

    generate
        if (BUF_OPERANDS) begin
            always_ff @(posedge clk_i or negedge async_rst_ni) begin : vproc_sld_stage_ex_valid
                if (~async_rst_ni) begin
                    state_ex_valid_q <= 1'b0;
                end
                else if (~sync_rst_ni) begin
                    state_ex_valid_q <= 1'b0;
                end
                else if (state_ex_ready) begin
                    state_ex_valid_q <= state_ex_valid_d;
                end
            end
            always_ff @(posedge clk_i) begin : vproc_sld_stage_ex
                if (state_ex_ready & state_ex_valid_d) begin
                    state_ex_q     <= state_ex_d;
                    operand_high_q <= operand_high_d;
                    v0msk_q        <= v0msk_d;
                end
            end
            assign state_ex_ready = ~state_ex_valid_q | state_res_ready;
        end else begin
            always_comb begin
                state_ex_valid_q = state_ex_valid_d;
                state_ex_q       = state_ex_d;
                operand_high_q   = operand_high_d;
                v0msk_q          = v0msk_d;
            end
            assign state_ex_ready = state_res_ready;
        end
        // low operand is always buffered
        always_ff @(posedge clk_i) begin
            if (state_ex_ready & state_ex_valid_d) begin
                operand_low_valid_q <= operand_low_valid_d;
                operand_low_q       <= operand_low_d;
            end
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
            assign state_res_ready = ~state_res_valid_q | pipe_out_ready_i;
        end else begin
            always_comb begin
                state_res_valid_q = state_ex_valid_q;
                state_res_q       = state_ex_q;
                result_q          = result_d;
                result_mask_q     = result_mask_d;
                write_mask_q      = write_mask_d;
            end
            assign state_res_ready = pipe_out_ready_i;
        end
    endgenerate


    ///////////////////////////////////////////////////////////////////////////
    // SLD OPERAND AND RESULT CONVERSION

    assign pipe_in_ready_o  = state_ex_ready;
    assign state_ex_valid_d = pipe_in_valid_i;
    assign v0msk_d          = pipe_in_mask_i;
    always_comb begin
        state_ex_d = pipe_in_ctrl_i;
        // overwrite rs1 with slide amount
        if (pipe_in_ctrl_i.mode.sld.slide1) begin
            if (pipe_in_ctrl_i.mode.sld.dir == SLD_UP) begin
                unique case (pipe_in_ctrl_i.eew)
                    VSEW_8:  state_ex_d.rs1.r.xval[$clog2(SLD_OP_W/8)-1:0] = {{$clog2(SLD_OP_W/8)-3{1'b0}}, 3'b001};
                    VSEW_16: state_ex_d.rs1.r.xval[$clog2(SLD_OP_W/8)-1:0] = {{$clog2(SLD_OP_W/8)-3{1'b0}}, 3'b010};
                    VSEW_32: state_ex_d.rs1.r.xval[$clog2(SLD_OP_W/8)-1:0] = {{$clog2(SLD_OP_W/8)-3{1'b0}}, 3'b100};
                    default: ;
                endcase
            end else begin
                unique case (pipe_in_ctrl_i.eew)
                    VSEW_8:  state_ex_d.rs1.r.xval[$clog2(SLD_OP_W/8)-1:0] = {{$clog2(SLD_OP_W/8)-3{1'b1}}, 3'b111};
                    VSEW_16: state_ex_d.rs1.r.xval[$clog2(SLD_OP_W/8)-1:0] = {{$clog2(SLD_OP_W/8)-3{1'b1}}, 3'b110};
                    VSEW_32: state_ex_d.rs1.r.xval[$clog2(SLD_OP_W/8)-1:0] = {{$clog2(SLD_OP_W/8)-3{1'b1}}, 3'b100};
                    default: ;
                endcase
            end
        end
    end

    // extract operands, substitute with rs1 when invalid to accomodate 1up and 1down operations
    always_comb begin
        operand_high_d      = pipe_in_op_i;
        operand_low_d       = DONT_CARE_ZERO ? '0 : 'x;
        operand_low_valid_d = 1'b0;
        if ((pipe_in_ctrl_i.mode.sld.dir == SLD_DOWN) & pipe_in_ctrl_i.mode.sld.slide1 &
            (pipe_in_ctrl_i.count.val[$clog2(VREG_W/SLD_OP_W)+2:0] == pipe_in_ctrl_i.vl[CFG_VL_W-1:$clog2(SLD_OP_W/8)])
        ) begin
            operand_high_d[31:0] = pipe_in_ctrl_i.rs1.r.xval;
        end
        unique case (pipe_in_ctrl_i.eew)
            VSEW_8: begin
                for (int i = 0; i < SLD_OP_W / 8 ; i++) begin
                    operand_low_d[i*8  +: 8 ] = pipe_in_ctrl_i.rs1.r.xval[7 :0];
                end
            end
            VSEW_16: begin
                for (int i = 0; i < SLD_OP_W / 16; i++) begin
                    operand_low_d[i*16 +: 16] = pipe_in_ctrl_i.rs1.r.xval[15:0];
                end
            end
            VSEW_32: begin
                for (int i = 0; i < SLD_OP_W / 32; i++) begin
                    operand_low_d[i*32 +: 32] = pipe_in_ctrl_i.rs1.r.xval;
                end
            end
            default: ;
        endcase
        if (~pipe_in_ctrl_i.first_cycle & state_ex_q.op_flags[0].vreg) begin // state_ex_q.rs2.vreg) begin
            operand_low_valid_d = 1'b1;
            for (int i = 0; i < SLD_OP_W / 8; i++) begin
                if (~pipe_in_ctrl_i.mode.sld.slide1 |
                    (pipe_in_ctrl_i.count.val[$clog2(VREG_W/SLD_OP_W)+2:0] != pipe_in_ctrl_i.vl[CFG_VL_W-1:$clog2(SLD_OP_W/8)]) |
                    (i <= pipe_in_ctrl_i.vl[$clog2(SLD_OP_W/8)-1:0])
                ) begin
                    operand_low_d[i*8 +: 8] = operand_high_q[i*8 +: 8];
                end
            end
        end
    end
    assign write_mask_d = v0msk_q;

    logic [VREG_W    -1:0] vl_mask;
    logic [SLD_OP_W/8-1:0] result_vl_mask, result_mask;
    assign vl_mask        = state_res_q.vl_0 ? {VREG_W{1'b0}} : ({VREG_W{1'b1}} >> (~state_res_q.vl));
    assign result_vl_mask = vl_mask[state_res_q.count.val[$clog2(VREG_W/SLD_OP_W)+2:0]*SLD_OP_W/8 +: SLD_OP_W/8];
    assign result_mask    = result_mask_q & result_vl_mask & (state_res_q.mode.sld.masked ? write_mask_q : {SLD_OP_W/8{1'b1}});

    assign pipe_out_valid_o = state_res_valid_q;
    assign pipe_out_ctrl_o  = state_res_q;
    assign pipe_out_res_o   = result_q;
    assign pipe_out_mask_o  = result_mask;


    ///////////////////////////////////////////////////////////////////////////
    // SLIDING OPERATION

    logic [$clog2(SLD_OP_W/8)-1:0] slide_bytes;
    assign slide_bytes = state_ex_q.rs1.r.xval[$clog2(SLD_OP_W/8)-1:0];

    always_comb begin
        result_d      = DONT_CARE_ZERO ? '0 : 'x;
        result_mask_d = DONT_CARE_ZERO ? '0 : 'x;

        for (int i = 0; i < SLD_OP_W/8; i++) begin
            if ($clog2(SLD_OP_W/8)'(i) < slide_bytes) begin
                result_d     [i*8 +: 8] = operand_low_q [($clog2(SLD_OP_W)'(SLD_OP_W/8 + i) - {3'b000, slide_bytes}) * 8 +: 8];
                result_mask_d[i]        = operand_low_valid_q;
            end else begin
                result_d     [i*8 +: 8] = operand_high_q[($clog2(SLD_OP_W)'(             i) - {3'b000, slide_bytes}) * 8 +: 8];
                result_mask_d[i]        = state_ex_q.op_flags[0].vreg; // state_ex_q.rs2.vreg;
            end
        end

        if (state_ex_q.mode.sld.slide1) begin
            result_mask_d = {(SLD_OP_W/8){1'b1}};
        end
    end


endmodule
