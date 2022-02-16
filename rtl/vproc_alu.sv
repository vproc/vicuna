// Copyright TU Wien
// Licensed under the Solderpad Hardware License v2.1, see LICENSE.txt for details
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1


module vproc_alu #(
        parameter int unsigned        VREG_W           = 128,  // width in bits of vector registers
        parameter int unsigned        CFG_VL_W         = 7,    // width of VL reg in bits (= log2(VREG_W))
        parameter int unsigned        ALU_OP_W         = 64,   // ALU operand width in bits
        parameter bit                 BUF_OPERANDS     = 1'b1, // insert pipeline stage after operand extraction
        parameter bit                 BUF_INTERMEDIATE = 1'b1, // insert pipeline stage for intermediate results
        parameter bit                 BUF_RESULTS      = 1'b1, // insert pipeline stage after computing result
        parameter type                CTRL_T           = logic,
        parameter bit                 DONT_CARE_ZERO   = 1'b0  // initialize don't care values to zero
    )(
        input  logic                  clk_i,
        input  logic                  async_rst_ni,
        input  logic                  sync_rst_ni,

        input  logic                  pipe_in_valid_i,
        output logic                  pipe_in_ready_o,
        input  CTRL_T                 pipe_in_ctrl_i,
        input  logic [ALU_OP_W  -1:0] pipe_in_op1_i,
        input  logic [ALU_OP_W  -1:0] pipe_in_op2_i,
        input  logic [ALU_OP_W/8-1:0] pipe_in_mask_i,

        output logic                  pipe_out_valid_o,
        input  logic                  pipe_out_ready_i,
        output CTRL_T                 pipe_out_ctrl_o,
        output logic [ALU_OP_W  -1:0] pipe_out_res_alu_o,
        output logic [ALU_OP_W/8-1:0] pipe_out_res_cmp_o,
        output logic [ALU_OP_W/8-1:0] pipe_out_mask_o
    );

    import vproc_pkg::*;


    ///////////////////////////////////////////////////////////////////////////
    // ALU BUFFERS

    logic  state_ex1_ready,                      state_ex2_ready,   state_res_ready;
    logic  state_ex1_valid_q, state_ex1_valid_d, state_ex2_valid_q, state_res_valid_q;
    CTRL_T state_ex1_q,       state_ex1_d,       state_ex2_q,       state_res_q;

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
            assign state_res_ready = ~state_res_valid_q | pipe_out_ready_i;
        end else begin
            always_comb begin
                state_res_valid_q = state_ex2_valid_q;
                state_res_q       = state_ex2_q;
                result_alu_q      = result_alu_d;
                result_cmp_q      = result_cmp_d;
                result_mask_q     = result_mask_d;
            end
            assign state_res_ready = pipe_out_ready_i;
        end
    endgenerate

    ///////////////////////////////////////////////////////////////////////////
    // ALU OPERAND AND RESULT CONVERSION

    logic [ALU_OP_W*9/8-1:0] operand1_9bpb;
    always_comb begin
        operand1_9bpb = DONT_CARE_ZERO ? '0 : 'x;
        for (int i = 0; i < ALU_OP_W / 8; i++) begin
            if (~pipe_in_ctrl_i.mode.alu.shift_op) begin
                operand1_9bpb[9*i+1 +: 8] = pipe_in_op1_i[8*i +: 8];
            end else begin
                operand1_9bpb[9*i   +: 8] = pipe_in_op1_i[8*i +: 8];
                unique case (pipe_in_ctrl_i.eew)
                    VSEW_8: begin
                        operand1_9bpb[9*i+8] =                  pipe_in_ctrl_i.mode.alu.sigext & pipe_in_op1_i[8*i+7];
                    end
                    VSEW_16: begin
                        operand1_9bpb[9*i+8] = ((i & 1) == 1) ? pipe_in_ctrl_i.mode.alu.sigext & pipe_in_op1_i[8*i+7] : pipe_in_op1_i[8*i+8];
                    end
                    VSEW_32: begin
                        operand1_9bpb[9*i+8] = ((i & 3) == 3) ? pipe_in_ctrl_i.mode.alu.sigext & pipe_in_op1_i[8*i+7] : pipe_in_op1_i[8*i+8];
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
            if (~pipe_in_ctrl_i.mode.alu.shift_op) begin
                operand2_9bpb[9*i+1 +: 8] = pipe_in_op2_i[8*i +: 8];
            end else begin
                operand2_9bpb[9*i   +: 8] = pipe_in_op2_i[8*i +: 8];
                unique case (pipe_in_ctrl_i.eew)
                    VSEW_8: begin
                        operand2_9bpb[9*i+8] =                  pipe_in_ctrl_i.mode.alu.sigext & pipe_in_op2_i[8*i+7];
                    end
                    VSEW_16: begin
                        operand2_9bpb[9*i+8] = ((i & 1) == 1) ? pipe_in_ctrl_i.mode.alu.sigext & pipe_in_op2_i[8*i+7] : pipe_in_op2_i[8*i+8];
                    end
                    VSEW_32: begin
                        operand2_9bpb[9*i+8] = ((i & 3) == 3) ? pipe_in_ctrl_i.mode.alu.sigext & pipe_in_op2_i[8*i+7] : pipe_in_op2_i[8*i+8];
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
            if (pipe_in_ctrl_i.mode.alu.op_mask == ALU_MASK_CARRY) begin
                carry_in_mask[i] = pipe_in_mask_i[i];
            end
            if (pipe_in_ctrl_i.mode.alu.shift_op) begin
                // Select carry in for averaging add/subtract rounding; the averaging add/subtract
                // instructions shift the result of the add/subtract right by one bit.  The result
                // is rounded based on its least significant bit as well as the bit that is shifted
                // out, depending on the rounding mode.  The carry in has the effect of rounding up
                // the result if the bit that is shifted out was set.
                unique case (pipe_in_ctrl_i.vxrm)
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
    assign state_vs2_subtract = pipe_in_ctrl_i.mode.alu.inv_op1 | pipe_in_ctrl_i.mode.alu.inv_op2;
    always_comb begin
        operand1_d = pipe_in_ctrl_i.mode.alu.inv_op1 ? ~operand1_9bpb : operand1_9bpb;
        operand2_d = pipe_in_ctrl_i.mode.alu.inv_op2 ? ~operand2_9bpb : operand2_9bpb;
        for (int i = 0; i < ALU_OP_W / 32; i++) begin
            // operands carry logic for fracturable adder
            operand1_d[36*i   ] =                                    carry_in_mask[i*4  ] ^ state_vs2_subtract;
            operand1_d[36*i+9 ] = (pipe_in_ctrl_i.eew == VSEW_8 ) ? (carry_in_mask[i*4+1] ^ state_vs2_subtract) : 1'b1;
            operand1_d[36*i+18] = (pipe_in_ctrl_i.eew != VSEW_32) ? (carry_in_mask[i*4+2] ^ state_vs2_subtract) : 1'b1;
            operand1_d[36*i+27] = (pipe_in_ctrl_i.eew == VSEW_8 ) ? (carry_in_mask[i*4+3] ^ state_vs2_subtract) : 1'b1;
            operand2_d[36*i   ] = 1'b1;
            operand2_d[36*i+9 ] = (pipe_in_ctrl_i.eew == VSEW_8 ) ? (carry_in_mask[i*4+1] ^ state_vs2_subtract) : 1'b0;
            operand2_d[36*i+18] = (pipe_in_ctrl_i.eew != VSEW_32) ? (carry_in_mask[i*4+2] ^ state_vs2_subtract) : 1'b0;
            operand2_d[36*i+27] = (pipe_in_ctrl_i.eew == VSEW_8 ) ? (carry_in_mask[i*4+3] ^ state_vs2_subtract) : 1'b0;
        end
    end

    assign pipe_in_ready_o   = state_ex1_ready;
    assign state_ex1_valid_d = pipe_in_valid_i;
    assign state_ex1_d       = pipe_in_ctrl_i;
    assign operand_mask_d    = pipe_in_mask_i;

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
    assign result_mask_d = ((state_ex2_q.mode.alu.op_mask == ALU_MASK_WRITE) ? operand_mask_tmp_q : {(ALU_OP_W/8){1'b1}}) & vl_mask[state_ex2_q.count.val*ALU_OP_W/8 +: ALU_OP_W/8];

    assign pipe_out_valid_o   = state_res_valid_q;
    assign pipe_out_ctrl_o    = state_res_q;
    always_comb begin
        // The result is inverted for averaging subtract instructions (i.e., instructions for
        // which the operands are shifted right and at least one operand is being inverted).
        // This is required to allow using the carry logic for rounding.
        pipe_out_res_alu_o = result_alu_q;
        if (state_res_q.mode.alu.shift_op & (state_res_q.mode.alu.inv_op1 | state_res_q.mode.alu.inv_op2)) begin
            pipe_out_res_alu_o = ~result_alu_q;
        end
    end
    assign pipe_out_res_cmp_o = result_cmp_q;
    assign pipe_out_mask_o    = result_mask_q;


    ///////////////////////////////////////////////////////////////////////////
    // ALU ARITHMETIC

    logic state_ex1_subtract;
    assign state_ex1_subtract = state_ex1_q.mode.alu.inv_op1 | state_ex1_q.mode.alu.inv_op2;

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
        unique case (state_ex1_q.mode.alu.opx1.sel)
            ALU_SEL_CARRY: cmp_d = state_ex1_subtract ? ~carry : carry;
            ALU_SEL_OVFLW: cmp_d = ovflw;
            ALU_SEL_LT:    cmp_d = ovflw ^ sig_res; // minuend is less than subtrahend
            ALU_SEL_MASK: begin
                for (int i = 0; i < ALU_OP_W / 8; i++) begin
                    unique case (state_ex1_q.mode.alu.op_mask)
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
        unique case (state_ex1_q.mode.alu.opx1.sel)
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
        unique case (state_ex1_q.mode.alu.opx1.shift)
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
        unique case ({state_ex1_q.mode.alu.opx1.shift, state_ex1_q.eew})

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
        unique case (state_ex2_q.mode.alu.opx2.res)
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
        unique case (state_ex2_q.mode.alu.opx2.cmp)
            ALU_CMP_CMP:  result_cmp_d =  cmp_q;
            ALU_CMP_CMPN: result_cmp_d = ~cmp_q;
            ALU_CMP_EQ:   result_cmp_d = ~neq;
            ALU_CMP_NE:   result_cmp_d =  neq;
            default: ;
        endcase
    end

endmodule
