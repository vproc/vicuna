// TODO DO THIS

module vproc_div_block #(
        parameter vproc_pkg::div_type  DIV_TYPE = vproc_pkg::DIV_GENERIC,
        parameter bit                  BUF_OPS  = 1'b0, // buffer operands (op1_i and op2_i)
        parameter bit                  BUF_DIV  = 1'b0, // buffer division result
        parameter bit                  BUF_RES  = 1'b0  // buffer final result (res_o)
        // Other parameters...
    )(
        input  logic                   clk_i,
        input  logic                   async_rst_ni,
        input  logic                   sync_rst_ni,

        input logic                    mod, // 0 = quotient, 1 = modulo

        input  logic [31:0]            op1_i,
        input  logic [31:0]            op2_i,

        output logic [31:0]            res_o

    );

    generate
        case (DIV_TYPE)

            vproc_pkg::DIV_GENERIC: begin

                logic [31:0] op1_q, op2_q;
                logic [31:0] div_q, div_d;
                logic [31:0] res_q, res_d;

                if (BUF_OPS) begin
                    always_ff @(posedge clk_i) begin
                        op1_q <= op1_i;
                        op2_q <= op2_i;
                    end
                end else begin
                    always_comb begin
                        op1_q = op1_i;
                        op2_q = op2_i;
                    end
                end

                if (BUF_DIV) begin
                    always_ff @(posedge clk_i) begin
                        div_q <= div_d;
                    end
                end else begin
                    always_comb begin
                        div_q = div_d;
                    end
                end

                if (BUF_RES) begin
                    always_ff @(posedge clk_i) begin
                        res_q <= res_d;
                    end
                end else begin
                    always_comb begin
                        res_q = res_d;
                    end
                end

                always_comb begin
                    unique case(mod)

                        // DIV/U
                        1'b0 : begin
                            div_d = $signed(op1_q) / $signed(op2_q);
                            if (op2_q == '0) begin
                                div_d = '1;
                            end
                            if (op1_q == {1'b1, {31{1'b0}}} && op2_q == '1) begin
                                div_d = op1_q;
                            end

                        end

                        // REM/U
                        1'b1 : begin
                            div_d = $signed(op1_q) % $signed(op2_q);
                            if (op2_q == 0) begin
                                div_d = op1_q;
                            end
                            if (op1_q == {1'b1, {31{1'b0}}} && op2_q == '1) begin
                                div_d = '0;
                            end
                        end
                        default: ;
                    endcase
                end

                assign res_d = div_q;
                assign res_o = res_q;

            end

            default: ;

        endcase
    endgenerate

endmodule
