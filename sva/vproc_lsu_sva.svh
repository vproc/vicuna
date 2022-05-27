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

    // Assert that there is no memory response transaction while dequeueing a suppressed request
    assert property (
        @(posedge clk_i)
        (deq_valid & xif_memres_if.mem_result_valid) |-> ~deq_state.suppressed
    ) else begin
        $error("incoming memory response transaction while dequeueing a suppressed request");
    end

    // Assert that there is no memory response transaction while dequeueing a failed request
    assert property (
        @(posedge clk_i)
        (deq_valid & xif_memres_if.mem_result_valid) |-> ~deq_state.exc
    ) else begin
        $error("incoming memory response transaction while dequeueing a failed request");
    end

    // Assert that the transaction complete queue is always ready
    assert property (
        @(posedge clk_i)
        trans_complete_valid |-> trans_complete_ready
    ) else begin
        $error("transaction complete queue is full");
    end

    // Assert that the instruction counter does not overflow
    assert property (
        @(posedge clk_i)
        (lsu_instr_cnt_q == '1) |-> (lsu_instr_cnt_d != '0)
    ) else begin
        $error("instruction counter overflowed");
    end
