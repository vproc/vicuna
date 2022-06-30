// Copyright TU Wien
// Licensed under the Solderpad Hardware License v2.1, see LICENSE.txt for details
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1

    // Assert that only the main core does not attempt to offload a speculative instruction
    assert property (
        @(posedge clk_i)
        xif_issue_if.issue_valid |-> instr_state_q[xif_issue_if.issue_req.id] != INSTR_SPECULATIVE
    ) else begin
        $error("attempt to offload instruction ID %d, which is still speculative",
               xif_issue_if.issue_req.id);
    end
