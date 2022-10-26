// TODO DO THIS

module vproc_div #(
        parameter int unsigned        DIV_OP_W     = 64,    // DIV unit operand width in bits (NOT PERMANENT)
        parameter vproc_pkg::div_type DIV_TYPE     = vproc_pkg::DIV_GENERIC,
        parameter bit                 BUF_OPERANDS = 1'b1,
        parameter bit                 BUF_DIV_IN   = 1'b1,
        parameter bit                 BUF_DIV_OUT  = 1'b1,
        parameter bit                 BUF_RESULTS  = 1'b1
        // parameter bit                 DONT_CARE_ZERO = 1'b0
    )(
        input  logic                  clk_i,
        input  logic                  async_rst_ni,
        input  logic                  sync_rst_ni,

        input  logic                  pipe_in_valid_i,
        output logic                  pipe_in_ready_o,
        
        output logic                  pipe_out_valid_o,
        input  logic                  pipe_out_ready_i
    );

    import vproc_pkg::*;

    ///////////////////////////////////////////////////////////////////////////
    // MUL BUFFERS

    logic  state_ex1_ready,                      state_ex2_ready,   state_ex3_ready,   state_res_ready;
    logic  state_ex1_valid_q, state_ex1_valid_d, state_ex2_valid_q, state_ex3_valid_q, state_res_valid_q;
    CTRL_T state_ex1_q,       state_ex1_d,       state_ex2_q,       state_ex3_q,       state_res_q;

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
            always_ff @(posedge c lk_i) begin : vproc_div_stage_ex1
                if (state_ex1_ready & state_ex1_valid_d) begin
                    state_ex1_q <= state_ex1_d;
                    operand1_q  <= operand1_d;
                    operand2_q  <= operand2_d;
                end
            end
            assign state_ex1_ready = ~state_ex1_valid_q | state_ex2_ready;
        end else begin
            always_comb begin
                state_ex1_valid_q = state_ex1_valid_d;
                state_ex1_q       = state_ex1_d;
                operand1_q        = operand1_d;
                operand2_q        = operand2_d;
            end
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
                end
            end
            assign state_ex2_ready = ~state_ex2_valid_q | state_ex3_ready;
        end else begin
            always_comb begin
                state_ex2_valid_q = state_ex1_valid_q;
                state_ex2_q       = state_ex1_q;
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
                end
            end
            assign state_ex3_ready = ~state_ex3_valid_q | state_res_ready;
        end else begin
            always_comb begin
                state_ex3_valid_q = state_ex2_valid_q;
                state_ex3_q       = state_ex2_q;
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
                end
            end
            assign state_res_ready = ~state_res_valid_q | pipe_out_ready_i;
        end else begin
            always_comb begin
                state_res_valid_q = state_ex3_valid_q;
                state_res_q       = state_ex3_q;
                result_q          = result_d;
            end
            assign state_res_ready = pipe_out_ready_i;
        end
    endgenerate

    logic [(DIV_OP_W/8)*17-1:0] div_op1, div_op2;

    // perform signed division of xx-bit integers
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
                .op1_i          (div_op1    [17*g +: 17] ),
                .op2_i          (div_op2    [17*g +: 17] ),
                .res_o          (div_res    [33*g +: 33] )
            );
        end
    endgenerate

    // compose result
    alwasy_comb begin

    end

endmodule

