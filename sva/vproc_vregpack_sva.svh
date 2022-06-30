// Copyright TU Wien
// Licensed under the Solderpad Hardware License v2.1, see LICENSE.txt for details
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1

    // Assert that the instruction ID is always valid
    assert property (
        @(posedge clk_i)
        stage_valid_q |-> instr_state_i[stage_state_q.instr_id] != INSTR_INVALID
    ) else begin
        $error("Instruction %d is invalid", stage_state_q.instr_id);
    end
