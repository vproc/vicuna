// Copyright TU Wien
// Licensed under the Solderpad Hardware License v2.1, see LICENSE.txt for details
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1

    // Assert that an empty result ID is not added twice
    assert property (
        @(posedge clk_i)
        result_empty_valid_i |-> ~instr_result_empty_q[result_empty_id_i]
    ) else begin
        $error("Empty result for instruction %d is requested again despite already being buffered",
               result_empty_id_i);
    end
