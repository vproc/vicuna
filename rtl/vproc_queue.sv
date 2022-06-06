// Copyright TU Wien
// Licensed under the Solderpad Hardware License v2.1, see LICENSE.txt for details
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1


module vproc_queue #(
        parameter int unsigned   WIDTH = 8,   // width of the queue (i.e., width of data elements)
        parameter int unsigned   DEPTH = 8,   // depth of the queue (i.e., max number of elements)
        parameter bit            FLOW  = 1'b0 // enable flow-through (pass data through if empty)
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
    logic [$clog2(DEPTH)-1:0] rd_pos_q,  rd_pos_d;  // read position
    logic [$clog2(DEPTH)-1:0] wr_pos_q,  wr_pos_d;  // write position
    logic                     last_wr_q, last_wr_d; // true if last access was write
    always_ff @(posedge clk_i or negedge async_rst_ni) begin
        if (~async_rst_ni) begin
            rd_pos_q  <= '0;
            wr_pos_q  <= '0;
            last_wr_q <= '0;
        end
        else if (~sync_rst_ni) begin
            rd_pos_q  <= '0;
            wr_pos_q  <= '0;
            last_wr_q <= '0;
        end else begin
            rd_pos_q  <= rd_pos_d;
            wr_pos_q  <= wr_pos_d;
            last_wr_q <= last_wr_d;
        end
    end

    logic empty, full;
    assign empty = (rd_pos_q == wr_pos_q) & ~last_wr_q;
    assign full  = (rd_pos_q == wr_pos_q) &  last_wr_q;

    always_ff @(posedge clk_i) begin
        if (~full) begin
            data[wr_pos_q] <= enq_data_i;
        end
    end

    logic push, pop;
    always_comb begin
        push        = 1'b0;
        pop         = 1'b0;
        enq_ready_o = 1'b0;
        deq_valid_o = 1'b0;
        deq_data_o  = data[rd_pos_q];
        if (~full) begin
            push        = enq_valid_i & (~FLOW | ~empty | ~deq_ready_i);
            enq_ready_o = 1'b1;
        end
        if (~empty) begin
            pop         = deq_ready_i;
            deq_valid_o = 1'b1;
        end
        else if (FLOW) begin
            deq_valid_o = enq_valid_i;
            deq_data_o  = enq_data_i;
        end
    end

    always_comb begin
        rd_pos_d  = rd_pos_q;
        wr_pos_d  = wr_pos_q;
        last_wr_d = last_wr_q;
        if (push) begin
            wr_pos_d  = (wr_pos_q == $clog2(DEPTH)'(DEPTH-1)) ? '0 : wr_pos_q + $clog2(DEPTH)'(1);
            last_wr_d = 1'b1;
        end
        if (pop) begin
            rd_pos_d  = (rd_pos_q == $clog2(DEPTH)'(DEPTH-1)) ? '0 : rd_pos_q + $clog2(DEPTH)'(1);
            last_wr_d = 1'b0;
        end
    end

    // Mask of valid entries
    logic [DEPTH-1:0] entry_valid;
    always_comb begin
        entry_valid = '0;
        if (rd_pos_q == wr_pos_q) begin
            // either all or no entries are valid, depending on last action
            entry_valid = {DEPTH{last_wr_q}};
        end else begin
            for (int i = 0; i < DEPTH; i++) begin
                if (rd_pos_q < wr_pos_q) begin
                    entry_valid[i] = (i >= rd_pos_q) & (i < wr_pos_q);
                end else begin
                    entry_valid[i] = (i >= rd_pos_q) | (i < wr_pos_q);
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
