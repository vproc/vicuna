// Copyright TU Wien
// Licensed under the Solderpad Hardware License v2.1, see LICENSE.txt for details
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1


// Simple single-port RAM with 32-bit words and byte enable
module ram32
    #(
        parameter SIZE = 16384, // 64 K
        parameter INIT_FILE
    )
    (
        input               clk_i,
        input               rst_ni,

        input               req_i,
        input               we_i,
        input        [ 3:0] be_i,
        input        [31:0] addr_i,
        input        [31:0] wdata_i,
        output logic        rvalid_o,
        output logic [31:0] rdata_o
    );

    localparam int ADDR_W = $clog2(SIZE);

    logic [31:0] mem[SIZE];
    logic [ADDR_W-1:0] mem_addr;
    assign mem_addr = addr_i[ADDR_W-1+2:2];

    always @(posedge clk_i) begin
        if (req_i && we_i) begin
            for (int i = 0; i < 4; i++)
                if (be_i[i] == 1'b1)
                    mem[mem_addr][i*8 +: 8] <= wdata_i[i*8 +: 8];
        end
        rdata_o <= mem[mem_addr];
    end

    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            rvalid_o <= '0;
        end else begin
            rvalid_o <= req_i;
        end
    end

    initial begin
        $readmemh(INIT_FILE, mem);
    end
endmodule
