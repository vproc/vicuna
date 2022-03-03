// Copyright TU Wien
// Licensed under the Solderpad Hardware License v2.1, see LICENSE.txt for details
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1

    // Assert that there is not attempt to stall the LSU output
    assert property (
        @(posedge clk_i)
        pipe_out_valid_o |-> pipe_out_ready_i
    ) else begin
        $error("attempt to stall LSU output");
    end
