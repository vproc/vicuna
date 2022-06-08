// Copyright TU Wien
// Licensed under the Solderpad Hardware License v2.1, see LICENSE.txt for details
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1


module vproc_vreg_wr_mux import vproc_pkg::*; #(
        parameter int unsigned                        VREG_W                  = 128,
        parameter int unsigned                        VPORT_WR_CNT            = 1,
        parameter int unsigned                        PIPE_CNT                = 1,
        parameter bit [UNIT_CNT-1:0]                  PIPE_UNITS   [PIPE_CNT] = '{'0},
        parameter int unsigned                        PIPE_VPORT_WR[PIPE_CNT] = '{0},
        parameter bit                                 STALL_PIPELINES         = '0,
        parameter bit                                 DONT_CARE_ZERO          = 1'b0  // initialize don't care values to zero
    )(
        input  logic                                  clk_i,
        input  logic                                  async_rst_ni,
        input  logic                                  sync_rst_ni,

        input  logic [PIPE_CNT    -1:0]               vreg_wr_valid_i,
        output logic [PIPE_CNT    -1:0]               vreg_wr_ready_o,
        input  logic [PIPE_CNT    -1:0][4:0]          vreg_wr_addr_i,
        input  logic [PIPE_CNT    -1:0][VREG_W/8-1:0] vreg_wr_be_i,
        input  logic [PIPE_CNT    -1:0][VREG_W  -1:0] vreg_wr_data_i,
        input  logic [PIPE_CNT    -1:0]               vreg_wr_clr_i,
        input  logic [PIPE_CNT    -1:0][1:0]          vreg_wr_clr_cnt_i,

        output logic [31:0]                           pend_vreg_wr_clr_o,

        output logic [VPORT_WR_CNT-1:0]               vregfile_wr_en_o,
        output logic [VPORT_WR_CNT-1:0][4:0]          vregfile_wr_addr_o,
        output logic [VPORT_WR_CNT-1:0][VREG_W/8-1:0] vregfile_wr_be_o,
        output logic [VPORT_WR_CNT-1:0][VREG_W  -1:0] vregfile_wr_data_o
    );

    localparam int unsigned VADDR_W = 5;

    // width of the pending write vreg clear counter (choosen such that it can span up to 1/4 of the
    // vector register addresses)
    localparam int unsigned PEND_CLEAR_CNT_W = $clog2(VADDR_W-1);

    function static int unsigned MAX_WR_ATTEMPTS(int unsigned PIPE_IDX);
        MAX_WR_ATTEMPTS = 1;
        for (int i = 0; i < PIPE_IDX; i++) begin
            if (PIPE_VPORT_WR[i] == PIPE_VPORT_WR[PIPE_IDX]) begin
                MAX_WR_ATTEMPTS += 1;
            end
        end
    endfunction

    logic [PIPE_CNT-1:0]                       vreg_wr_valid;
    logic [PIPE_CNT-1:0][4:0]                  vreg_wr_addr;
    logic [PIPE_CNT-1:0][VREG_W/8        -1:0] vreg_wr_be;
    logic [PIPE_CNT-1:0][VREG_W          -1:0] vreg_wr_data;
    logic [PIPE_CNT-1:0]                       vreg_wr_clr;
    logic [PIPE_CNT-1:0][PEND_CLEAR_CNT_W-1:0] vreg_wr_clr_cnt;
    generate
        for (genvar i = 0; i < PIPE_CNT; i++) begin
            localparam int unsigned PIPE_MAX_WR_ATTEMPTS = MAX_WR_ATTEMPTS(i);
            localparam int unsigned MAX_WR_DELAY         = (1 << (PIPE_MAX_WR_ATTEMPTS - 1)) - 1;
            localparam int unsigned WRITE_BUFFER_SZ      = (MAX_WR_DELAY > 0) ? MAX_WR_DELAY : 1;

            logic                        vreg_wr_valid_q  [WRITE_BUFFER_SZ], vreg_wr_valid_d;
            logic [VADDR_W         -1:0] vreg_wr_addr_q   [WRITE_BUFFER_SZ], vreg_wr_addr_d;
            logic [VREG_W/8        -1:0] vreg_wr_be_q     [WRITE_BUFFER_SZ], vreg_wr_be_d;
            logic [VREG_W          -1:0] vreg_wr_data_q   [WRITE_BUFFER_SZ], vreg_wr_data_d;
            logic                        vreg_wr_clr_q    [WRITE_BUFFER_SZ], vreg_wr_clr_d;
            logic [PEND_CLEAR_CNT_W-1:0] vreg_wr_clr_cnt_q[WRITE_BUFFER_SZ], vreg_wr_clr_cnt_d;
            always_ff @(posedge clk_i) begin
                vreg_wr_valid_q  [0] <= vreg_wr_valid_d;
                vreg_wr_addr_q   [0] <= vreg_wr_addr_d;
                vreg_wr_be_q     [0] <= vreg_wr_be_d;
                vreg_wr_data_q   [0] <= vreg_wr_data_d;
                vreg_wr_clr_q    [0] <= vreg_wr_clr_d;
                vreg_wr_clr_cnt_q[0] <= vreg_wr_clr_cnt_d;
                for (int j = 1; j < MAX_WR_DELAY; j++) begin
                    vreg_wr_valid_q  [j] <= vreg_wr_valid_q  [j-1];
                    vreg_wr_addr_q   [j] <= vreg_wr_addr_q   [j-1];
                    vreg_wr_be_q     [j] <= vreg_wr_be_q     [j-1];
                    vreg_wr_data_q   [j] <= vreg_wr_data_q   [j-1];
                    vreg_wr_clr_q    [j] <= vreg_wr_clr_q    [j-1];
                    vreg_wr_clr_cnt_q[j] <= vreg_wr_clr_cnt_q[j-1];
                end
            end
            assign vreg_wr_valid_d   = vreg_wr_valid_i  [i];
            assign vreg_wr_data_d    = vreg_wr_data_i   [i];
            assign vreg_wr_be_d      = vreg_wr_be_i     [i];
            assign vreg_wr_addr_d    = vreg_wr_addr_i   [i];
            assign vreg_wr_clr_d     = vreg_wr_clr_i    [i];
            assign vreg_wr_clr_cnt_d = vreg_wr_clr_cnt_i[i];

            if (~STALL_PIPELINES) begin
                always_comb begin
                    vreg_wr_valid  [i] = vreg_wr_valid_d;
                    vreg_wr_addr   [i] = vreg_wr_addr_d;
                    vreg_wr_be     [i] = vreg_wr_be_d;
                    vreg_wr_data   [i] = vreg_wr_data_d;
                    vreg_wr_clr    [i] = vreg_wr_clr_d;
                    vreg_wr_clr_cnt[i] = vreg_wr_clr_cnt_d;
                    for (int j = 0; j < MAX_WR_DELAY; j++) begin
                        if ((((j + 1) & (j + 2)) == 0) & vreg_wr_valid_q[j]) begin
                            vreg_wr_valid  [i] = 1'b1;
                            vreg_wr_addr   [i] = vreg_wr_addr_q   [j];
                            vreg_wr_be     [i] = vreg_wr_be_q     [j];
                            vreg_wr_data   [i] = vreg_wr_data_q   [j];
                            vreg_wr_clr    [i] = vreg_wr_clr_q    [j];
                            vreg_wr_clr_cnt[i] = vreg_wr_clr_cnt_q[j];
                        end
                    end
                end
            end else begin
                assign vreg_wr_valid  [i] = vreg_wr_valid_i  [i];
                assign vreg_wr_addr   [i] = vreg_wr_addr_i   [i];
                assign vreg_wr_be     [i] = vreg_wr_be_i     [i];
                assign vreg_wr_data   [i] = vreg_wr_data_i   [i];
                assign vreg_wr_clr    [i] = vreg_wr_clr_i    [i];
                assign vreg_wr_clr_cnt[i] = vreg_wr_clr_cnt_i[i];
            end
        end
    endgenerate

    always_comb begin
        vreg_wr_ready_o    = '1;
        vregfile_wr_en_o   = '0;
        vregfile_wr_addr_o = DONT_CARE_ZERO ? '0 : 'x;
        vregfile_wr_be_o   = DONT_CARE_ZERO ? '0 : 'x;
        vregfile_wr_data_o = DONT_CARE_ZERO ? '0 : 'x;
        for (int i = 0; i < VPORT_WR_CNT; i++) begin
            for (int j = 0; j < PIPE_CNT; j++) begin
                if ((i == PIPE_VPORT_WR[j]) & vreg_wr_valid[j]) begin
                    vregfile_wr_en_o  [i] = 1'b1;
                    vregfile_wr_addr_o[i] = vreg_wr_addr[j];
                    vregfile_wr_be_o  [i] = vreg_wr_be  [j];
                    vregfile_wr_data_o[i] = vreg_wr_data[j];
                    if (STALL_PIPELINES) begin
                        // clear ready signal for higher index pipelines using the same write port
                        for (int k = j + 1; k < PIPE_CNT; k++) begin
                            if (i == PIPE_VPORT_WR[k]) begin
                                vreg_wr_ready_o[k] = 1'b0;
                            end
                        end
                    end
                    break;
                end
            end
        end
    end

    logic [PIPE_CNT-1:0][31:0] pipe_pend_vreg_wr_clr;
    generate
        for (genvar i = 0; i < PIPE_CNT; i++) begin
            localparam bit VPORT_PEND_CLR_BULK = PIPE_UNITS[i][UNIT_ELEM];

            logic                        pend_clr;
            logic [PEND_CLEAR_CNT_W-1:0] pend_clr_cnt;
            logic [VADDR_W         -1:0] pend_clr_addr;
            logic [VADDR_W         -1:0] pend_clr_addr_mask;
            assign pend_clr           = vreg_wr_clr    [i];
            assign pend_clr_cnt       = vreg_wr_clr_cnt[i];
            assign pend_clr_addr      = vreg_wr_addr   [i];
            assign pend_clr_addr_mask = {VADDR_W{1'b1}} << pend_clr_cnt;
            always_comb begin
                pipe_pend_vreg_wr_clr[i] = '0;
                if (pend_clr) begin
                    if (VPORT_PEND_CLR_BULK) begin
                        for (int j = 0; j < (1<<VADDR_W); j++) begin
                            pipe_pend_vreg_wr_clr[i][j] = (VADDR_W'(j)   & pend_clr_addr_mask) ==
                                                          (pend_clr_addr & pend_clr_addr_mask);
                        end
                    end else begin
                        pipe_pend_vreg_wr_clr[i][pend_clr_addr] = 1'b1;
                    end
                end
            end
        end
    endgenerate
    always_comb begin
        pend_vreg_wr_clr_o = '0;
        for (int i = 0; i < PIPE_CNT; i++) begin
            pend_vreg_wr_clr_o |= pipe_pend_vreg_wr_clr[i];
        end
    end

endmodule
