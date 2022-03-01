// Copyright TU Wien
// Licensed under the Solderpad Hardware License v2.1, see LICENSE.txt for details
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1


module vproc_vreg_wr_mux #(
        parameter int unsigned                         VREG_W          = 128,
        parameter int unsigned                         VPORT_WR_CNT    = 1,
        parameter int unsigned                         PIPE_CNT        = 2,
        parameter bit [VPORT_WR_CNT-1:0][PIPE_CNT-1:0] VPORT_WR_MAP    = '0,
        parameter bit                                  STALL_PIPELINES = '0,
        parameter bit                                  DONT_CARE_ZERO  = 1'b0  // initialize don't care values to zero
    )(
        input  logic [PIPE_CNT    -1:0]                vreg_wr_valid_i,
        output logic [PIPE_CNT    -1:0]                vreg_wr_ready_o,
        input  logic [PIPE_CNT    -1:0][4:0]           vreg_wr_addr_i,
        input  logic [PIPE_CNT    -1:0][VREG_W/8-1:0]  vreg_wr_be_i,
        input  logic [PIPE_CNT    -1:0][VREG_W  -1:0]  vreg_wr_data_i,

        output logic [VPORT_WR_CNT-1:0]                vregfile_wr_en_o,
        output logic [VPORT_WR_CNT-1:0][4:0]           vregfile_wr_addr_o,
        output logic [VPORT_WR_CNT-1:0][VREG_W/8-1:0]  vregfile_wr_be_o,
        output logic [VPORT_WR_CNT-1:0][VREG_W  -1:0]  vregfile_wr_data_o
    );

    always_comb begin
        vreg_wr_ready_o    = '1;
        vregfile_wr_en_o   = '0;
        vregfile_wr_addr_o = DONT_CARE_ZERO ? '0 : 'x;
        vregfile_wr_be_o   = DONT_CARE_ZERO ? '0 : 'x;
        vregfile_wr_data_o = DONT_CARE_ZERO ? '0 : 'x;
        for (int i = 0; i < VPORT_WR_CNT; i++) begin
            for (int j = 0; j < PIPE_CNT; j++) begin
                if (VPORT_WR_MAP[i][j] & vreg_wr_valid_i[j]) begin
                    vregfile_wr_en_o  [i] = 1'b1;
                    vregfile_wr_addr_o[i] = vreg_wr_addr_i[j];
                    vregfile_wr_be_o  [i] = vreg_wr_be_i  [j];
                    vregfile_wr_data_o[i] = vreg_wr_data_i[j];
                    if (STALL_PIPELINES) begin
                        // clear ready signal for higher index pipelines using the same write port
                        vreg_wr_ready_o  &= ~(VPORT_WR_MAP[i] & ({PIPE_CNT{1'b1}} << (j + 1)));
                    end
                    break;
                end
            end
        end
    end

endmodule
