// TODO DO THIS

module vproc_div #(
        parameter int unsigned        DIV_OP_W     = 64,    // DIV unit operand width in bits (NOT PERMANENT)
        parameter vproc_pkg::div_type DIV_TYPE     = vproc_pkg::DIV_GENERIC,
        parameter bit                 BUF_OPERANDS = 1'b1,
        parameter bit                 BUF_DIV_IN   = 1'b1,
        parameter bit                 BUF_DIV_OUT  = 1'b1,
        parameter bit                 BUF_RESULTS  = 1'b1,
        parameter type                CTRL_T       = logic
        // parameter bit                 DONT_CARE_ZERO = 1'b0
    )(
        input  logic                  clk_i,
        input  logic                  async_rst_ni,
        input  logic                  sync_rst_ni,

        input  logic                  pipe_in_valid_i,
        output logic                  pipe_in_ready_o,

        input  CTRL_T                 pipe_in_ctrl_i,
        input  logic [DIV_OP_W  -1:0] pipe_in_op1_i,
        input  logic [DIV_OP_W  -1:0] pipe_in_op2_i,
        input  logic [DIV_OP_W  -1:0] pipe_in_op3_i,
        input  logic [DIV_OP_W/8-1:0] pipe_in_mask_i,
        
        output logic                  pipe_out_valid_o,
        input  logic                  pipe_out_ready_i,

        output CTRL_T                 pipe_out_ctrl_o,
        output logic [DIV_OP_W  -1:0] pipe_out_res_o,
        output logic [DIV_OP_W/8-1:0] pipe_out_mask_o
    );

    import vproc_pkg::*;

    ///////////////////////////////////////////////////////////////////////////
    // MUL BUFFERS

    logic  state_ex1_ready,                      state_ex2_ready,   state_ex3_ready,   state_res_ready;
    logic  state_ex1_valid_q, state_ex1_valid_d, state_ex2_valid_q, state_ex3_valid_q, state_res_valid_q;
    CTRL_T state_ex1_q,       state_ex1_d,       state_ex2_q,       state_ex3_q,       state_res_q;

    logic [DIV_OP_W  -1:0] operand1_q,     operand1_d;
    logic [DIV_OP_W  -1:0] operand2_q,     operand2_d;
    logic [DIV_OP_W/8-1:0] operand_mask_q, operand_mask_d;
    logic [DIV_OP_W  -1:0] result_q,       result_d;
    logic [DIV_OP_W/8-1:0] result_mask1_q, result_mask1_d; //  mask out stage 1 buffer (MUL_IN)
    logic [DIV_OP_W/8-1:0] result_mask2_q, result_mask2_d; //  mask out stage 2 buffer (MUL_OUT)
    logic [DIV_OP_W/8-1:0] result_mask3_q, result_mask3_d; //  mask out stage 3 buffer (RESULTS)
                                                            // needed for vregunpack to mask write destinations
    generate
        if (BUF_OPERANDS) begin
            always_ff @(posedge clk_i or negedge async_rst_ni) begin : vproc_div_stage_ex1_valid
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
            always_ff @(posedge clk_i) begin : vproc_div_stage_ex1
                if (state_ex1_ready & state_ex1_valid_d) begin
                    state_ex1_q <= state_ex1_d;
                    operand1_q  <= operand1_d;
                    operand2_q  <= operand2_d;
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
                operand_mask_q <= operand_mask_d;
            end
            assign state_ex1_ready = state_ex2_ready;
        end

        if (BUF_DIV_IN) begin
            always_ff @(posedge clk_i or negedge async_rst_ni) begin : vproc_div_stage_ex2_valid
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
            always_ff @(posedge clk_i) begin : vproc_div_stage_ex2
                if (state_ex2_ready & state_ex1_valid_q) begin
                    state_ex2_q    <= state_ex1_q;
                    result_mask1_q <= result_mask1_d;
                end
            end
            assign state_ex2_ready = ~state_ex2_valid_q | state_ex3_ready;
        end else begin
            always_comb begin
                state_ex2_valid_q = state_ex1_valid_q;
                state_ex2_q       = state_ex1_q;
                result_mask1_q    = result_mask1_d;
            end
            assign state_ex2_ready = state_ex3_ready;
        end

        if (BUF_DIV_OUT) begin
            always_ff @(posedge clk_i or negedge async_rst_ni) begin : vproc_div_stage_ex3_valid
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
            always_ff @(posedge clk_i) begin : vproc_div_stage_ex3
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
            always_ff @(posedge clk_i or negedge async_rst_ni) begin : vproc_div_stage_res_valid
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
            always_ff @(posedge clk_i) begin : vproc_div_stage_res
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
    // DIV ARITHMETIC

    logic [DIV_OP_W/8-1:0] op1_signs, op2_signs;
    always_comb begin
        op1_signs = DONT_CARE_ZERO ? '0 : 'x;
        op2_signs = DONT_CARE_ZERO ? '0 : 'x;
        for (int i = 0; i < DIV_OP_W/8; i++) begin
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

    logic [(DIV_OP_W/8)*17-1:0] div_op1, div_op2;
    always_comb begin
        div_op1 = DONT_CARE_ZERO ? '0 : 'x;
        for (int i = 0; i < DIV_OP_W / 32; i++) begin
            div_op1[68*i +: 68] = {
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
        div_op2 = DONT_CARE_ZERO ? '0 : 'x;
        for (int i = 0; i < DIV_OP_W / 32; i++) begin
            div_op2[68*i +: 68] = {
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

    // Not sure if this is needed...
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

    // perform unsigned division of xx-bit integers
    logic [(DIV_TOP_W/8)*33-1:0] div_res;
    genvar g;
    generate
        for (g = 0; g < DIV_OP_W / 8; g++) begin
            vproc_div_block #(
                .DIV_TYPE       (DIV_TYPE                ),
                .BUF_OPS        (BUF_DIV_IN              ),
                .BUF_DIV        (BUF_DIV_OUT             ),
                .BUF_RES        (1'b0                    )
            ) div_block (
                .clk_i          (clk_i                   ),
                .async_rst_ni   (async_rst_ni            ),
                .sync_rst_ni    (sync_rst_ni             ),
                .mod            (                        ), // tells div_block to mod or not
                .op1_i          (div_op1    [17*g +: 17] ),
                .op2_i          (div_op2    [17*g +: 17] ),
                .res_o          (div_res    [33*g +: 33] )
            );
        end
    endgenerate

    // compose result
    always_comb begin

    end

endmodule

