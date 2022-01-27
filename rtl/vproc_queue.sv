// Copyright TU Wien
// Licensed under the Solderpad Hardware License v2.1, see LICENSE.txt for details
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1


module vproc_queue #(
        parameter int unsigned   WIDTH = 8,
        parameter int unsigned   DEPTH = 8
    )(
        input  logic             clk_i,
        input  logic             async_rst_ni,
        input  logic             sync_rst_ni,

        output logic             enq_ready_o,
        input  logic             enq_valid_i,
        input  logic [WIDTH-1:0] enq_data_i,

        input  logic             deq_ready_i,
        output logic             deq_valid_o,
        output logic [WIDTH-1:0] deq_data_o,

        output logic [WIDTH-1:0] flags_any_o,
        output logic [WIDTH-1:0] flags_all_o
    );

    logic [WIDTH-1:0]         data[DEPTH];
    logic [$clog2(DEPTH)-1:0] rd_pos, wr_pos; // read and write positions
    logic                     last_wr;        // true if last access was write

    always_ff @(posedge clk_i or negedge async_rst_ni) begin
        if (~async_rst_ni) begin
            rd_pos  <= '0;
            wr_pos  <= '0;
            last_wr <= '0;
        end
        else if (~sync_rst_ni) begin
            rd_pos  <= '0;
            wr_pos  <= '0;
            last_wr <= '0;
        end else begin
            if (enq_ready_o & enq_valid_i) begin
                wr_pos       <= (wr_pos == $clog2(DEPTH)'(DEPTH-1)) ? '0 : wr_pos + 1;
                last_wr      <= 1'b1;
            end
            if (deq_ready_i & deq_valid_o) begin
                rd_pos       <= (rd_pos == $clog2(DEPTH)'(DEPTH-1)) ? '0 : rd_pos + 1;
                last_wr      <= 1'b0;
            end
        end
    end
    always_ff @(posedge clk_i) begin
        if (enq_ready_o & enq_valid_i) begin
            data[wr_pos] <= enq_data_i;
        end
    end

    assign enq_ready_o = (rd_pos != wr_pos) | ~last_wr;
    assign deq_valid_o = (rd_pos != wr_pos) |  last_wr;
    assign deq_data_o  = data[rd_pos];

    // Mask of valid entries
    logic [DEPTH-1:0] entry_valid;
    always_comb begin
        entry_valid = '0;
        if (rd_pos == wr_pos) begin
            // either all or no entries are valid, depending on last action
            entry_valid = {DEPTH{last_wr}};
        end else begin
            for (int i = 0; i < DEPTH; i++) begin
                if (rd_pos < wr_pos) begin
                    entry_valid[i] = (i >= rd_pos) & (i < wr_pos);
                end else begin
                    entry_valid[i] = (i >= rd_pos) | (i < wr_pos);
                end
            end
        end
    end

    // Bitwise AND and OR of all valid entries (allows to check whether a flag
    // is set in any/all valid entries)
    always_comb begin
        flags_any_o = {WIDTH{1'b0}};
        flags_all_o = {WIDTH{1'b1}};
        for (int i = 0; i < DEPTH; i++) begin
            if (entry_valid[i]) begin
                flags_any_o |= data[i];
                flags_all_o &= data[i];
            end
        end
    end

endmodule
