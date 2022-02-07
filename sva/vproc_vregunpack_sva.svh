// Copyright TU Wien
// Licensed under the Solderpad Hardware License v2.1, see LICENSE.txt for details
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1

    // Assert that the requested vreg read addresses correspond to the registers being fetched
    generate
        for (genvar i = 0; i < OP_CNT; i++) begin
            assert property (
                @(posedge clk_i)
                op_addressing[i] |-> (vreg_rd_addr_o[OP_SRC[i]] == op_vreg_addr[i])
            ) else begin
                $error("incorrect vreg read address for operand %d", i);
            end
        end
    endgenerate

    // Assert that a vreg is still in the pending reads while being fetched
    generate
        for (genvar i = 0; i < OP_CNT; i++) begin
            assert property (
                @(posedge clk_i)
                op_addressing[i] |-> pending_vreg_reads_o[vreg_rd_addr_o[OP_SRC[i]]]
            ) else begin
                $error("fetched vreg not in pending reads");
            end
        end
    endgenerate
