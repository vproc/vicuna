// Copyright TU Wien
// Licensed under the ISC license, see LICENSE.txt for details
// SPDX-License-Identifier: ISC


// minimalistic simulation top module with clock gen and initial reset

module demo_tb #(
        parameter              MAIN_CORE  = "",
        parameter              RAM_FPATH  = "",
        parameter int unsigned RAM_SIZE   = 262144,
        parameter bit          DIFF_CLK   = 1'b0,
        parameter real         SYSCLK_PER = 0.0,
        parameter int unsigned PLL_MUL    = 10,
        parameter int unsigned PLL_DIV    = 20
    );

    logic clk, rst;
    logic rx, tx;

    demo_top #(
        .MAIN_CORE  ( MAIN_CORE  ),
        .RAM_FPATH  ( RAM_FPATH  ),
        .RAM_SIZE   ( RAM_SIZE   ),
        .DIFF_CLK   ( DIFF_CLK   ),
        .SYSCLK_PER ( SYSCLK_PER ),
        .PLL_MUL    ( PLL_MUL    ),
        .PLL_DIV    ( PLL_DIV    )
    ) soc (
        .sys_clk_pi ( clk        ),
        .sys_clk_ni ( ~clk       ),
        .sys_rst_ni ( ~rst       ),
        .uart_rx_i  ( rx         ),
        .uart_tx_o  ( tx         )
    );

    initial begin
        rst = 1'b1;
        #(SYSCLK_PER*10);
        rst = 1'b0;
    end

    always begin
        clk = 1'b0;
        #(SYSCLK_PER/2);
        clk = 1'b1;
        #(SYSCLK_PER/2);
    end

    assign rx = 1'b1;
endmodule
