// Copyright TU Wien
// Licensed under the Solderpad Hardware License v2.1, see LICENSE.txt for details
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1

    // Assert that there are never two simultaneous reads from the same vreg read port
    generate
        for (genvar i = 0; i < OP_CNT; i++) begin
            for (genvar j = i + 1; j < OP_CNT; j++) begin
                if (OP_SRC[i] == OP_SRC[j]) begin
                    assert property (
                        @(posedge clk_i)
                        op_addressing[i] |-> ~op_addressing[j]
                    ) else begin
                        $error("simultaneous addressing for operands %d and %d sharing port %d",
                               i, j, OP_SRC[i]);
                    end
                end
            end
        end
    endgenerate

    // Assert that the requested vreg read addresses correspond to the registers being fetched
    generate
        for (genvar i = 0; i < OP_CNT; i++) begin
            if (OP_SRC[i] < VPORT_CNT) begin
                assert property (
                    @(posedge clk_i)
                    op_addressing[i] |-> (vreg_rd_addr_o[OP_SRC[i]] == op_vreg_addr[i])
                ) else begin
                    $error("incorrect vreg read address for operand %d", i);
                end
            end
        end
    endgenerate

    // Assert that a vreg is still in the pending reads while being fetched
    generate
        for (genvar i = 0; i < OP_CNT; i++) begin
            if ((OP_SRC[i] < VPORT_CNT) & ~OP_DYN_ADDR[i]) begin
                assert property (
                    @(posedge clk_i)
                    op_addressing[i] |-> pending_vreg_reads_o[vreg_rd_addr_o[OP_SRC[i]]]
                ) else begin
                    $error("fetched vreg not in pending reads");
                end
            end
        end
    endgenerate
