// Copyright TU Wien
// Licensed under the ISC license, see LICENSE.txt for details
// SPDX-License-Identifier: ISC


module vproc_mul_block #(
        parameter vproc_pkg::mul_type MUL_TYPE = vproc_pkg::MUL_GENERIC,
        parameter bit                 BUF_OPS, // buffer operands (op1_i and op2_i)
        parameter bit                 BUF_MUL, // buffer multiplication result (and acc_i)
        parameter bit                 BUF_RES  // buffer final result (res_o)
    )(
        input  logic                  clk_i,
        input  logic                  rst_ni,

        input  logic [16:0]           op1_i,
        input  logic [16:0]           op2_i,

        // note that when operands are buffered, then acc*_i must be delayed by 1 cycle
        input  logic [15:0]           acc_i,
        input  logic                  acc_flag_i, // use accumulator (otherwise it is replaced with 0)
        input  logic                  acc_sub_i,  // subtract multiplication result from accumulator instead of adding

        output logic [32:0] res_o
    );

    generate
        case (MUL_TYPE)

            vproc_pkg::MUL_GENERIC: begin

                logic [16:0] op1_q, op2_q;
                logic [15:0] acc_q;
                logic        acc_sub_q;
                logic [32:0] mul_q, mul_d;
                logic [32:0] res_q, res_d;

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

                if (BUF_MUL) begin
                    always_ff @(posedge clk_i) begin
                        mul_q     <= mul_d;
                        acc_q     <= acc_flag_i ? acc_i : '0;
                        acc_sub_q <= acc_sub_i;
                    end
                end else begin
                    always_comb begin
                        mul_q     = mul_d;
                        acc_q     = acc_flag_i ? acc_i : '0;
                        acc_sub_q = acc_sub_i;
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

                assign mul_d = $signed(op1_q) * $signed(op2_q);
                assign res_d = acc_sub_i ? {17'b0, acc_q} - mul_q : {17'b0, acc_q} + mul_q;
                assign res_o = res_q;

            end

            vproc_pkg::MUL_XLNX_DSP48E1: begin

                logic [6:0] opmode;
                logic [3:0] alumode;
                assign opmode  = {1'b0 , acc_flag_i ? 2'b11 : 2'b00, 4'b0101};
                assign alumode = {2'b00, acc_sub_i  ? 2'b11 : 2'b00         };

                logic [47:0] mul_res;
                DSP48E1 #(
                    .A_INPUT            ( "DIRECT"                 ),
                    .B_INPUT            ( "DIRECT"                 ),
                    .USE_DPORT          ( "FALSE"                  ),
                    .USE_MULT           ( "MULTIPLY"               ),
                    .INMODEREG          ( 0                        ),
                    .OPMODEREG          ( BUF_MUL ? 1 : 0          ),
                    .ALUMODEREG         ( BUF_MUL ? 1 : 0          ),
                    .CARRYINREG         ( 0                        ),
                    .CARRYINSELREG      ( 0                        ),
                    .AREG               ( BUF_OPS ? 1 : 0          ),
                    .BREG               ( BUF_OPS ? 1 : 0          ),
                    .MREG               ( BUF_MUL ? 1 : 0          ),
                    .CREG               ( BUF_MUL ? 1 : 0          ),
                    .PREG               ( BUF_RES ? 1 : 0          )
                ) xlnx_dsp48e1_inst (
                    .CLK                ( clk_i                    ),
                    // inputs and outputs
                    .INMODE             ( '0                       ),
                    .OPMODE             ( opmode                   ),
                    .ALUMODE            ( alumode                  ),
                    .CARRYINSEL         ( '0                       ),
                    .CARRYIN            ( '0                       ),
                    .A                  ( {{13{op1_i[16]}}, op1_i} ),
                    .B                  ( {    op2_i[16]  , op2_i} ),
                    .C                  ( {32'b0, acc_i}           ),
                    .P                  ( mul_res                  ),
                    // clock enable and reset config
                    .CEINMODE           ( 1'b0                     ),
                    .CECTRL             ( BUF_MUL                  ),
                    .CEALUMODE          ( BUF_MUL                  ),
                    .CECARRYIN          ( 1'b0                     ),
                    .CEA1               ( 1'b0                     ),
                    .CEA2               ( BUF_OPS                  ),
                    .CEAD               ( 1'b0                     ),
                    .CEB1               ( 1'b0                     ),
                    .CEB2               ( BUF_OPS                  ),
                    .CEC                ( BUF_MUL                  ),
                    .CED                ( 1'b0                     ),
                    .CEM                ( BUF_MUL                  ),
                    .CEP                ( BUF_RES                  ),
                    .RSTA               ( 1'b0                     ),
                    .RSTALLCARRYIN      ( 1'b0                     ),
                    .RSTALUMODE         ( 1'b0                     ),
                    .RSTB               ( 1'b0                     ),
                    .RSTC               ( 1'b0                     ),
                    .RSTCTRL            ( 1'b0                     ),
                    .RSTD               ( 1'b0                     ),
                    .RSTINMODE          ( 1'b0                     ),
                    .RSTM               ( 1'b0                     ),
                    .RSTP               ( 1'b0                     ),
                    // unused inputs
                    .D                  ( '1                       ),
                    .ACIN               ( '1                       ),
                    .BCIN               ( '1                       ),
                    .CARRYCASCIN        ( '1                       ),
                    .MULTSIGNIN         ( '1                       ),
                    .PCIN               ( '1                       ),
                    // unused outputs
                    .ACOUT              (                          ),
                    .BCOUT              (                          ),
                    .CARRYCASCOUT       (                          ),
                    .MULTSIGNOUT        (                          ),
                    .PCOUT              (                          ),
                    .OVERFLOW           (                          ),
                    .PATTERNBDETECT     (                          ),
                    .PATTERNDETECT      (                          ),
                    .UNDERFLOW          (                          ),
                    .CARRYOUT           (                          )
                );
                assign res_o = mul_res[32:0];

            end

        endcase
    endgenerate

endmodule
