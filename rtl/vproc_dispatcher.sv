// Copyright TU Wien
// Licensed under the Solderpad Hardware License v2.1, see LICENSE.txt for details
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1


module vproc_dispatcher #(
        parameter int unsigned                            PIPE_CNT       = 1,
        parameter vproc_pkg::op_unit                      UNIT[PIPE_CNT] = '{vproc_pkg::UNIT_ALU},
        parameter int unsigned                            MAX_VADDR_W    = 5,    // max addr width
        parameter type                                    DECODER_DATA_T = logic,
        parameter bit                                     DONT_CARE_ZERO = 1'b0  // initialize don't care values to zero
    )(
        input  logic                                      clk_i,
        input  logic                                      async_rst_ni,
        input  logic                                      sync_rst_ni,

        input  logic                                      instr_valid_i,
        output logic                                      instr_ready_o,
        input  DECODER_DATA_T                             instr_data_i,     // decoder data
        input  logic [(1<<MAX_VADDR_W)-1:0]               instr_vreg_wr_i,  // vreg write map

        output logic [PIPE_CNT-1:0]                       dispatch_valid_o,
        input  logic [PIPE_CNT-1:0]                       dispatch_ready_i,
        output DECODER_DATA_T                             dispatch_data_o,

        output logic               [(1<<MAX_VADDR_W)-1:0] pend_vreg_wr_map_o,
        input  logic [PIPE_CNT-1:0][(1<<MAX_VADDR_W)-1:0] pend_vreg_wr_clear_i
    );

    import vproc_pkg::*;

    localparam int unsigned VADDR_CNT = 1 << MAX_VADDR_W;

    // Pending vector register writes
    logic [VADDR_CNT-1:0] pend_vreg_wr_map_q, pend_vreg_wr_map_d; // active pending vreg writes
    always_ff @(posedge clk_i or negedge async_rst_ni) begin : vproc_hazard_reg
        if (~async_rst_ni) begin
            pend_vreg_wr_map_q <= '0;
        end
        else if (~sync_rst_ni) begin
            pend_vreg_wr_map_q <= '0;
        end else begin
            pend_vreg_wr_map_q <= pend_vreg_wr_map_d;
        end
    end
    assign pend_vreg_wr_map_o = pend_vreg_wr_map_q;

    logic [VADDR_CNT-1:0] pend_vreg_wr_map_set;   // add pending vreg writes
    logic [VADDR_CNT-1:0] pend_vreg_wr_map_clr;   // remove pending vreg writes
    always_comb begin
        pend_vreg_wr_map_d = (pend_vreg_wr_map_q & ~pend_vreg_wr_map_clr) | pend_vreg_wr_map_set;
    end

    // Dispatch next instruction
    always_comb begin
        dispatch_valid_o = '0;
        if (instr_valid_i & ((instr_vreg_wr_i & pend_vreg_wr_map_q) == '0)) begin
            for (int i = 0; i < PIPE_CNT; i++) begin
                if (instr_data_i.unit == UNIT[i]) begin
                    dispatch_valid_o[i] = 1'b1;
                end
            end
        end
    end
    assign dispatch_data_o = instr_data_i;

    // Complete the input handshake upon dispatch and add the pending vreg writes of the dispatched
    // instruction to the map
    always_comb begin
        instr_ready_o        = 1'b0;
        pend_vreg_wr_map_set = '0;
        if ((dispatch_valid_o & dispatch_ready_i) != '0) begin
            instr_ready_o        = 1'b1;
            pend_vreg_wr_map_set = instr_vreg_wr_i;
        end
    end

    // Clearing pending vreg writes
    always_comb begin
        pend_vreg_wr_map_clr = '0;
        for (int i = 0; i < PIPE_CNT; i++) begin
            pend_vreg_wr_map_clr |= pend_vreg_wr_clear_i[i];
        end
    end

endmodule
