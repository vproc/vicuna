// Copyright TU Wien
// Licensed under the Solderpad Hardware License v2.1, see LICENSE.txt for details
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1


module vproc_result #(
        parameter int unsigned      XIF_ID_W       = 3,    // width in bits of instruction IDs
        parameter bit               DONT_CARE_ZERO = 1'b0  // initialize don't care values to zero
    )(
        input  logic                clk_i,
        input  logic                async_rst_ni,
        input  logic                sync_rst_ni,

        input  logic                result_lsu_valid_i,
        input  logic [XIF_ID_W-1:0] result_lsu_id_i,
        input  logic                result_lsu_exc_i,
        input  logic [5:0]          result_lsu_exccode_i,

        input  logic                result_xreg_valid_i,
        input  logic [XIF_ID_W-1:0] result_xreg_id_i,
        input  logic [4:0]          result_xreg_addr_i,
        input  logic [31:0]         result_xreg_data_i,

        input  logic                result_empty_valid_i,
        output logic                result_empty_ready_o,
        input  logic [XIF_ID_W-1:0] result_empty_id_i,

        input  logic                result_vl_valid_i,
        output logic                result_vl_ready_o,
        input  logic [XIF_ID_W-1:0] result_vl_id_i,
        input  logic [4:0]          result_vl_addr_i,
        input  logic [31:0]         result_vl_data_i,

        vproc_xif.coproc_result     xif_result_if
    );

    // LSU result buffer
    logic                result_lsu_valid_q,   result_lsu_valid_d;
    logic [XIF_ID_W-1:0] result_lsu_id_q,      result_lsu_id_d;
    logic                result_lsu_exc_q,     result_lsu_exc_d;
    logic [5:0]          result_lsu_exccode_q, result_lsu_exccode_d;

    // XREG result buffer
    logic                result_xreg_valid_q, result_xreg_valid_d;
    logic [XIF_ID_W-1:0] result_xreg_id_q,    result_xreg_id_d;
    logic [4:0]          result_xreg_addr_q,  result_xreg_addr_d;
    logic [31:0]         result_xreg_data_q,  result_xreg_data_d;

    // empty result buffer
    logic                result_empty_valid_q, result_empty_valid_d;
    logic [XIF_ID_W-1:0] result_empty_id_q,    result_empty_id_d;

    // CFG result buffer
    logic                result_vl_valid_q, result_vl_valid_d;
    logic [XIF_ID_W-1:0] result_vl_id_q,    result_vl_id_d;
    logic [4:0]          result_vl_addr_q,  result_vl_addr_d;

    always_ff @(posedge clk_i or negedge async_rst_ni) begin : vproc_result_valid
        if (~async_rst_ni) begin
            result_lsu_valid_q   <= 1'b0;
            result_xreg_valid_q  <= 1'b0;
            result_empty_valid_q <= 1'b0;
            result_vl_valid_q    <= 1'b0;
        end
        else if (~sync_rst_ni) begin
            result_lsu_valid_q   <= 1'b0;
            result_xreg_valid_q  <= 1'b0;
            result_empty_valid_q <= 1'b0;
            result_vl_valid_q    <= 1'b0;
        end
        else begin
            result_lsu_valid_q   <= result_lsu_valid_d;
            result_xreg_valid_q  <= result_xreg_valid_d;
            result_empty_valid_q <= result_empty_valid_d;
            result_vl_valid_q    <= result_vl_valid_d;
        end
    end
    always_ff @(posedge clk_i) begin : vproc_result
        result_lsu_id_q      <= result_lsu_id_d;
        result_lsu_exc_q     <= result_lsu_exc_d;
        result_lsu_exccode_q <= result_lsu_exccode_d;
        result_xreg_id_q     <= result_xreg_id_d;
        result_xreg_addr_q   <= result_xreg_addr_d;
        result_xreg_data_q   <= result_xreg_data_d;
        result_empty_id_q    <= result_empty_id_d;
        result_vl_id_q       <= result_vl_id_d;
        result_vl_addr_q     <= result_vl_addr_d;
    end

    typedef enum logic [2:0] {
        RESULT_SOURCE_LSU_IN,
        RESULT_SOURCE_LSU_BUF,
        RESULT_SOURCE_XREG_IN,
        RESULT_SOURCE_XREG_BUF,
        RESULT_SOURCE_EMPTY_BUF,
        RESULT_SOURCE_VL_BUF,
        RESULT_SOURCE_NONE
    } result_source_e;
    result_source_e result_source;
    always_comb begin
        result_source = RESULT_SOURCE_NONE;

        // LSU always takes precedence (does not require a buffer)
        if (result_lsu_valid_q) begin
            result_source = RESULT_SOURCE_LSU_BUF;
        end
        else if (result_lsu_valid_i) begin
            result_source = RESULT_SOURCE_LSU_IN;
        end
        // XREG goes second
        else if (result_xreg_valid_q) begin
            result_source = RESULT_SOURCE_XREG_BUF;
        end
        else if (result_xreg_valid_i) begin
            result_source = RESULT_SOURCE_XREG_IN;
        end
        // empty results go third
        else if (result_empty_valid_q) begin
            result_source = RESULT_SOURCE_EMPTY_BUF;
        end
        // CFG goes last (since it is the most recent instruction and the only
        // result that can be stalled; the CFG result always comes from the
        // buffer, since the config registers need an extra cycle to update)
        else if (result_vl_valid_q) begin
            result_source = RESULT_SOURCE_VL_BUF;
        end
    end

    always_comb begin
        result_lsu_valid_d   = result_lsu_valid_q;
        result_lsu_id_d      = result_lsu_id_q;
        result_lsu_exc_d     = result_lsu_exc_q;
        result_lsu_exccode_d = result_lsu_exccode_q;
        result_xreg_valid_d  = result_xreg_valid_q;
        result_xreg_addr_d   = result_xreg_addr_q;
        result_xreg_data_d   = result_xreg_data_q;
        result_xreg_id_d     = result_xreg_id_q;
        result_empty_valid_d = result_empty_valid_q;
        result_empty_id_d    = result_empty_id_q;
        result_vl_valid_d    = result_vl_valid_q;
        result_vl_id_d       = result_vl_id_q;
        result_vl_addr_d     = result_vl_addr_q;

        if (result_source == RESULT_SOURCE_LSU_BUF) begin
            result_lsu_valid_d = ~xif_result_if.result_ready;
        end
        if (result_source == RESULT_SOURCE_XREG_BUF) begin
            result_xreg_valid_d = ~xif_result_if.result_ready;
        end
        if (result_source == RESULT_SOURCE_EMPTY_BUF) begin
            result_empty_valid_d = ~xif_result_if.result_ready;
        end
        if (result_source == RESULT_SOURCE_VL_BUF) begin
            result_vl_valid_d = ~xif_result_if.result_ready;
        end

        if (result_lsu_valid_i) begin
            result_lsu_valid_d   = ~xif_result_if.result_ready | (result_source != RESULT_SOURCE_LSU_IN);
            result_lsu_id_d      = result_lsu_id_i;
            result_lsu_exc_d     = result_lsu_exc_i;
            result_lsu_exccode_d = result_lsu_exccode_i;
        end
        if (result_xreg_valid_i) begin
            result_xreg_valid_d = ~xif_result_if.result_ready | (result_source != RESULT_SOURCE_XREG_IN);
            result_xreg_id_d    = result_xreg_id_i;
            result_xreg_addr_d  = result_xreg_addr_i;
            result_xreg_data_d  = result_xreg_data_i;
        end
        if (result_empty_valid_i) begin
            result_empty_valid_d = 1'b1;    // empty result is always buffered
            result_empty_id_d    = result_empty_id_i;
        end
        if (result_vl_valid_i) begin
            result_vl_valid_d = 1'b1;       // CFG result is always buffered
            result_vl_id_d    = result_vl_id_i;
            result_vl_addr_d  = result_vl_addr_i;
        end
    end

    assign result_empty_ready_o = ((result_source == RESULT_SOURCE_EMPTY_BUF) & xif_result_if.result_ready) | ~result_empty_valid_q;
    assign result_vl_ready_o    = ((result_source == RESULT_SOURCE_VL_BUF   ) & xif_result_if.result_ready) | ~result_vl_valid_q;

    always_comb begin
        xif_result_if.result_valid   = '0;
        xif_result_if.result.id      = DONT_CARE_ZERO ? '0 : 'x;
        xif_result_if.result.data    = DONT_CARE_ZERO ? '0 : 'x;
        xif_result_if.result.rd      = DONT_CARE_ZERO ? '0 : 'x;
        xif_result_if.result.we      = '0;
        xif_result_if.result.exc     = '0;
        xif_result_if.result.exccode = DONT_CARE_ZERO ? '0 : 'x;

        unique case (result_source)
            RESULT_SOURCE_LSU_BUF: begin
                xif_result_if.result_valid   = 1'b1;
                xif_result_if.result.id      = result_lsu_id_q;
                xif_result_if.result.exc     = result_lsu_exc_q;
                xif_result_if.result.exccode = result_lsu_exccode_q;
            end
            RESULT_SOURCE_LSU_IN: begin
                xif_result_if.result_valid   = 1'b1;
                xif_result_if.result.id      = result_lsu_id_i;
                xif_result_if.result.exc     = result_lsu_exc_i;
                xif_result_if.result.exccode = result_lsu_exccode_i;
            end
            RESULT_SOURCE_XREG_BUF: begin
                xif_result_if.result_valid = 1'b1;
                xif_result_if.result.id    = result_xreg_id_q;
                xif_result_if.result.data  = result_xreg_data_q;
                xif_result_if.result.rd    = result_xreg_addr_q;
                xif_result_if.result.we    = 1'b1;
            end
            RESULT_SOURCE_XREG_IN: begin
                xif_result_if.result_valid = 1'b1;
                xif_result_if.result.id    = result_xreg_id_i;
                xif_result_if.result.data  = result_xreg_data_i;
                xif_result_if.result.rd    = result_xreg_addr_i;
                xif_result_if.result.we    = 1'b1;
            end
            RESULT_SOURCE_EMPTY_BUF: begin
                xif_result_if.result_valid = 1'b1;
                xif_result_if.result.id    = result_empty_id_q;
            end
            RESULT_SOURCE_VL_BUF: begin
                xif_result_if.result_valid = 1'b1;
                xif_result_if.result.id    = result_vl_id_q;
                xif_result_if.result.data  = result_vl_data_i; // data not buffered
                xif_result_if.result.rd    = result_vl_addr_q;
                xif_result_if.result.we    = 1'b1;
            end
            default: ;
        endcase
    end


`ifdef VPROC_SVA
`include "vproc_result_sva.svh"
`endif

endmodule
