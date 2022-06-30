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

    // Assert that the main core does not commit a valid instruction that is not speculative
    assert property (
        @(posedge clk_i)
        xif_commit_if.commit_valid |-> (
            (instr_state_q[xif_commit_if.commit.id] != INSTR_COMMITTED) &
            (instr_state_q[xif_commit_if.commit.id] != INSTR_KILLED)
        )
    ) else begin
        $error("attempt to commit instruction ID %d, which already had a commit transaction",
               xif_commit_if.commit.id);
    end
