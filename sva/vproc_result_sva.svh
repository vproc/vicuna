// Copyright TU Wien
// Licensed under the ISC license, see LICENSE.txt for details
// SPDX-License-Identifier: ISC

    // Assert that the result buffers do not overflow
    assert property (
        @(posedge clk_i)
        (result_lsu_valid_i & result_lsu_valid_q) |->
        (xif_result_if.result_ready)
    ) else begin
        $error("LSU result buffer overflows");
    end
    assert property (
        @(posedge clk_i)
        (result_xreg_valid_i & result_xreg_valid_q) |->
        (xif_result_if.result_ready & ~result_lsu_valid_i & ~result_lsu_valid_q)
    ) else begin
        $error("XREG result buffer overflows");
    end
    assert property (
        @(posedge clk_i)
        (result_empty_valid_i & result_empty_valid_q) |->
        (xif_result_if.result_ready & ~result_lsu_valid_i & ~result_lsu_valid_q & ~result_xreg_valid_i & ~result_xreg_valid_q)
    ) else begin
        $error("Empty result buffer overflows");
    end
    assert property (
        @(posedge clk_i)
        (result_vl_valid_i & result_vl_valid_q) |->
        (xif_result_if.result_ready & ~result_lsu_valid_i & ~result_lsu_valid_q & ~result_xreg_valid_i & ~result_xreg_valid_q & ~result_empty_valid_q)
    ) else begin
        $error("VL result buffer overflows");
    end
