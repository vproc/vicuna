// Copyright TU Wien
// Licensed under the Solderpad Hardware License v2.1, see LICENSE.txt for details
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1


module vproc_mul #(
        parameter int unsigned        MUL_OP_W       = 64,   // MUL unit operand width in bits
        parameter vproc_pkg::mul_type MUL_TYPE       = vproc_pkg::MUL_GENERIC,
        parameter bit                 BUF_OPERANDS   = 1'b1, // insert pipeline stage after operand extraction
        parameter bit                 BUF_MUL_IN     = 1'b1, // insert pipeline stage before HW multiplication
        parameter bit                 BUF_MUL_OUT    = 1'b1, // insert pipeline stage after HW multiplication
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
        input  logic [MUL_OP_W  -1:0] pipe_in_op1_i,
        input  logic [MUL_OP_W  -1:0] pipe_in_op2_i,
        input  logic [MUL_OP_W  -1:0] pipe_in_op3_i,
        input  logic [MUL_OP_W/8-1:0] pipe_in_mask_i,

        output logic                  pipe_out_valid_o,
        input  logic                  pipe_out_ready_i,
        output CTRL_T                 pipe_out_ctrl_o,
        output logic [MUL_OP_W  -1:0] pipe_out_res_o,
        output logic [MUL_OP_W/8-1:0] pipe_out_mask_o
    );

    import vproc_pkg::*;


    ///////////////////////////////////////////////////////////////////////////
    // MUL BUFFERS

    logic  state_ex1_ready,                      state_ex2_ready,   state_ex3_ready,   state_res_ready;
    logic  state_ex1_valid_q, state_ex1_valid_d, state_ex2_valid_q, state_ex3_valid_q, state_res_valid_q;
    CTRL_T state_ex1_q,       state_ex1_d,       state_ex2_q,       state_ex3_q,       state_res_q;

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
            assign state_res_ready = ~state_res_valid_q | pipe_out_ready_i;
        end else begin
            always_comb begin
                state_res_valid_q = state_ex3_valid_q;
                state_res_q       = state_ex3_q;
                result_q          = result_d;
                result_mask3_q    = result_mask3_d;
            end
            assign state_res_ready = pipe_out_ready_i;
        end
    endgenerate


    ///////////////////////////////////////////////////////////////////////////
    // MUL OPERAND AND RESULT CONVERSION

    assign pipe_in_ready_o   = state_ex1_ready;
    assign state_ex1_valid_d = pipe_in_valid_i;
    assign state_ex1_d       = pipe_in_ctrl_i;
    assign operand1_d        = pipe_in_op1_i;
    assign operand2_d        = pipe_in_op2_i;
    assign accumulator1_d    = pipe_in_op3_i;
    assign operand_mask_d    = pipe_in_mask_i;

    // result byte mask
    logic [MUL_OP_W/8-1:0] vl_mask;
    assign vl_mask        = ~state_ex1_q.vl_part_0 ? ({(MUL_OP_W/8){1'b1}} >> (~state_ex1_q.vl_part)) : '0;
    assign result_mask1_d = (state_ex1_q.mode.mul.masked ? operand_mask_q : {(MUL_OP_W/8){1'b1}}) & vl_mask;

    assign result_mask2_d = result_mask1_q;
    assign result_mask3_d = result_mask2_q;

    assign pipe_out_valid_o = state_res_valid_q;
    assign pipe_out_ctrl_o  = state_res_q;
    assign pipe_out_res_o   = result_q;
    assign pipe_out_mask_o  = result_mask3_q;


    ///////////////////////////////////////////////////////////////////////////
    // MUL ARITHMETIC

    logic [MUL_OP_W/8-1:0] op1_signs, op2_signs;
    always_comb begin
        op1_signs = DONT_CARE_ZERO ? '0 : 'x;
        op2_signs = DONT_CARE_ZERO ? '0 : 'x;
        for (int i = 0; i < MUL_OP_W/8; i++) begin
            op1_signs[i] = state_ex1_q.mode.mul.op1_signed & operand1_q[8*i+7];
            op2_signs[i] = state_ex1_q.mode.mul.op2_signed & operand2_q[8*i+7];
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
        unique case (state_ex1_q.mode.mul.op)
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
        unique case (state_ex2_q.mode.mul.op)
            MUL_VMUL:  mul_accflag = 1'b0;
            MUL_VMULH: mul_accflag = 1'b0;
            MUL_VSMUL: mul_accflag = 1'b1;
            MUL_VMACC: mul_accflag = 1'b1;
            default: ;
        endcase
    end
    assign mul_accsub = state_ex2_q.mode.mul.accsub;

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
                .ops_valid_i  ( state_ex2_ready & state_ex1_valid_q),
                .mul_valid_i  ( state_ex3_ready & state_ex2_valid_q),
                .res_valid_i  ( state_res_ready & state_ex3_valid_q),
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
        unique case (state_ex3_q.mode.mul.op)

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
