// Copyright TU Wien
// Licensed under the Solderpad Hardware License v2.1, see LICENSE.txt for details
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1


module vproc_unit_mux #(
        parameter bit [vproc_pkg::UNIT_CNT-1:0]      UNITS           = '0,
        parameter int unsigned                       XIF_ID_W        = 3,
        parameter int unsigned                       XIF_ID_CNT      = 8,
        parameter int unsigned                       VREG_W          = 128,
        parameter int unsigned                       OP_CNT          = 2,
        parameter int unsigned                       MAX_OP_W        = 32,
        parameter int unsigned                       RES_CNT         = 2,
        parameter int unsigned                       MAX_RES_W       = 32,
        parameter vproc_pkg::mul_type                MUL_TYPE        = vproc_pkg::MUL_GENERIC,
        parameter bit                                ADDR_ALIGNED    = 1'b1,
        parameter type                               CTRL_T          = logic,
        parameter type                               COUNTER_T       = logic,
        parameter int unsigned                       COUNTER_W       = 0,
        parameter bit                                DONT_CARE_ZERO  = 1'b0
    )
    (
        input  logic                                 clk_i,
        input  logic                                 async_rst_ni,
        input  logic                                 sync_rst_ni,

        input  logic                                 pipe_in_valid_i,
        output logic                                 pipe_in_ready_o,
        input  CTRL_T                                pipe_in_ctrl_i,
        input  logic    [OP_CNT -1:0][MAX_OP_W -1:0] pipe_in_op_data_i,

        output logic                                 pipe_out_valid_o,
        input  logic                                 pipe_out_ready_i,
        output logic    [XIF_ID_W              -1:0] pipe_out_instr_id_o,
        output vproc_pkg::cfg_vsew                   pipe_out_eew_o,
        output logic    [4:0]                        pipe_out_vaddr_o,
        output logic    [RES_CNT-1:0]                pipe_out_res_store_o,
        output logic    [RES_CNT-1:0]                pipe_out_res_valid_o,
        output vproc_pkg::pack_flags [RES_CNT  -1:0] pipe_out_res_flags_o,
        output logic    [RES_CNT-1:0][MAX_RES_W-1:0] pipe_out_res_data_o,
        output logic    [RES_CNT-1:0][MAX_RES_W-1:0] pipe_out_res_mask_o,
        output logic                                 pipe_out_pend_clear_o,
        output logic    [1:0]                        pipe_out_pend_clear_cnt_o,
        output logic                                 pipe_out_instr_done_o,

        output logic                                 pending_load_o,
        output logic                                 pending_store_o,

        input  logic    [31:0]                       vreg_pend_rd_i,

        input  logic    [XIF_ID_CNT            -1:0] instr_spec_i,
        input  logic    [XIF_ID_CNT            -1:0] instr_killed_i,
        output logic                                 instr_done_valid_o,
        output logic    [XIF_ID_W              -1:0] instr_done_id_o,

        vproc_xif.coproc_mem                         xif_mem_if,
        vproc_xif.coproc_mem_result                  xif_memres_if,

        output logic                                 trans_complete_valid_o,
        output logic    [XIF_ID_W              -1:0] trans_complete_id_o,
        output logic                                 trans_complete_exc_o,
        output logic    [5:0]                        trans_complete_exccode_o,

        output logic                                 xreg_valid_o,
        output logic    [XIF_ID_W              -1:0] xreg_id_o,
        output logic    [4:0]                        xreg_addr_o,
        output logic    [31:0]                       xreg_data_o
    );

    import vproc_pkg::*;

    logic [UNIT_CNT-1:0] unit_in_valid;
    logic [UNIT_CNT-1:0] unit_in_ready;
    always_comb begin
        unit_in_valid                      = '0;
        //unit_in_valid[pipe_in_ctrl_i.unit] = pipe_in_valid_i;
        //pipe_in_ready_o                    = unit_in_ready[pipe_in_ctrl_i.unit];

        // TODO remove below code and replace with code above
        unit_in_valid   = {UNIT_CNT{pipe_in_valid_i}};
        pipe_in_ready_o = '0;
        for (int i = 0; i < UNIT_CNT; i++) begin
            if (UNITS[i]) begin
                pipe_in_ready_o |= unit_in_ready[i];
            end
        end
    end

    logic      [UNIT_CNT-1:0]                             unit_out_valid;
    logic      [UNIT_CNT-1:0]                             unit_out_ready;
    logic      [UNIT_CNT-1:0][XIF_ID_W              -1:0] unit_out_instr_id;
    cfg_vsew   [UNIT_CNT-1:0]                             unit_out_eew;
    logic      [UNIT_CNT-1:0][4:0]                        unit_out_vaddr;
    logic      [UNIT_CNT-1:0][RES_CNT-1:0]                unit_out_res_store;
    logic      [UNIT_CNT-1:0][RES_CNT-1:0]                unit_out_res_valid;
    pack_flags [UNIT_CNT-1:0][RES_CNT-1:0]                unit_out_res_flags;
    logic      [UNIT_CNT-1:0][RES_CNT-1:0][MAX_RES_W-1:0] unit_out_res_data;
    logic      [UNIT_CNT-1:0][RES_CNT-1:0][MAX_RES_W-1:0] unit_out_res_mask;
    logic      [UNIT_CNT-1:0]                             unit_out_pend_clear;
    logic      [UNIT_CNT-1:0][1:0]                        unit_out_pend_clear_cnt;
    logic      [UNIT_CNT-1:0]                             unit_out_instr_done;
    generate
        for (genvar i = 0; i < UNIT_CNT; i++) begin
            if (UNITS[i]) begin
                // LSU-related signals
                vproc_xif #(
                    .X_ID_WIDTH  ( XIF_ID_W ),
                    .X_MEM_WIDTH ( MAX_OP_W )
                ) unit_xif ();
                logic                pending_load;
                logic                pending_store;
                logic                instr_done_valid;
                logic [XIF_ID_W-1:0] instr_done_id;
                logic                trans_complete_valid;
                logic [XIF_ID_W-1:0] trans_complete_id;
                logic                trans_complete_exc;
                logic [5:0]          trans_complete_exccode;

                // ELEM-related signals (for XREG writeback)
                logic                xreg_valid;
                logic [XIF_ID_W-1:0] xreg_id;
                logic [4:0]          xreg_addr;
                logic [31:0]         xreg_data;

                vproc_unit_wrapper #(
                    .UNIT                      ( op_unit'(i)                ),
                    .XIF_ID_W                  ( XIF_ID_W                   ),
                    .XIF_ID_CNT                ( XIF_ID_CNT                 ),
                    .VREG_W                    ( VREG_W                     ),
                    .OP_CNT                    ( OP_CNT                     ),
                    .MAX_OP_W                  ( MAX_OP_W                   ),
                    .RES_CNT                   ( RES_CNT                    ),
                    .MAX_RES_W                 ( MAX_RES_W                  ),
                    .MUL_TYPE                  ( MUL_TYPE                   ),
                    .ADDR_ALIGNED              ( ADDR_ALIGNED               ),
                    .CTRL_T                    ( CTRL_T                     ),
                    .COUNTER_T                 ( COUNTER_T                  ),
                    .COUNTER_W                 ( COUNTER_W                  ),
                    .DONT_CARE_ZERO            ( DONT_CARE_ZERO             )
                ) unit (
                    .clk_i                     ( clk_i                      ),
                    .async_rst_ni              ( async_rst_ni               ),
                    .sync_rst_ni               ( sync_rst_ni                ),
                    .pipe_in_valid_i           ( unit_in_valid          [i] ),
                    .pipe_in_ready_o           ( unit_in_ready          [i] ),
                    .pipe_in_ctrl_i            ( pipe_in_ctrl_i             ),
                    .pipe_in_op_data_i         ( pipe_in_op_data_i          ),
                    .pipe_out_valid_o          ( unit_out_valid         [i] ),
                    .pipe_out_ready_i          ( unit_out_ready         [i] ),
                    .pipe_out_instr_id_o       ( unit_out_instr_id      [i] ),
                    .pipe_out_eew_o            ( unit_out_eew           [i] ),
                    .pipe_out_vaddr_o          ( unit_out_vaddr         [i] ),
                    .pipe_out_res_store_o      ( unit_out_res_store     [i] ),
                    .pipe_out_res_valid_o      ( unit_out_res_valid     [i] ),
                    .pipe_out_res_flags_o      ( unit_out_res_flags     [i] ),
                    .pipe_out_res_data_o       ( unit_out_res_data      [i] ),
                    .pipe_out_res_mask_o       ( unit_out_res_mask      [i] ),
                    .pipe_out_pend_clear_o     ( unit_out_pend_clear    [i] ),
                    .pipe_out_pend_clear_cnt_o ( unit_out_pend_clear_cnt[i] ),
                    .pipe_out_instr_done_o     ( unit_out_instr_done    [i] ),
                    .pending_load_o            ( pending_load               ),
                    .pending_store_o           ( pending_store              ),
                    .vreg_pend_rd_i            ( vreg_pend_rd_i             ),
                    .instr_spec_i              ( instr_spec_i               ),
                    .instr_killed_i            ( instr_killed_i             ),
                    .instr_done_valid_o        ( instr_done_valid           ),
                    .instr_done_id_o           ( instr_done_id              ),
                    .xif_mem_if                ( unit_xif                   ),
                    .xif_memres_if             ( unit_xif                   ),
                    .trans_complete_valid_o    ( trans_complete_valid       ),
                    .trans_complete_id_o       ( trans_complete_id          ),
                    .trans_complete_exc_o      ( trans_complete_exc         ),
                    .trans_complete_exccode_o  ( trans_complete_exccode     ),
                    .xreg_valid_o              ( xreg_valid                 ),
                    .xreg_id_o                 ( xreg_id                    ),
                    .xreg_addr_o               ( xreg_addr                  ),
                    .xreg_data_o               ( xreg_data                  )
                );

                if (op_unit'(i) == UNIT_LSU) begin
                    assign pending_load_o            = pending_load;
                    assign pending_store_o           = pending_store;
                    assign instr_done_valid_o        = instr_done_valid;
                    assign instr_done_id_o           = instr_done_id;
                    assign xif_mem_if.mem_valid      = unit_xif.mem_valid;
                    assign unit_xif.mem_ready        = xif_mem_if.mem_ready;
                    assign xif_mem_if.mem_req.addr   = unit_xif.mem_req.addr;
                    assign xif_mem_if.mem_req.we     = unit_xif.mem_req.we;
                    assign xif_mem_if.mem_req.be     = unit_xif.mem_req.be;
                    assign xif_mem_if.mem_req.wdata  = unit_xif.mem_req.wdata;
                    assign unit_xif.mem_resp.exc     = xif_mem_if.mem_resp.exc;
                    assign unit_xif.mem_resp.exccode = xif_mem_if.mem_resp.exccode;
                    assign unit_xif.mem_resp.dbg     = xif_mem_if.mem_resp.dbg;
                    assign unit_xif.mem_result_valid = xif_memres_if.mem_result_valid;
                    assign unit_xif.mem_result.id    = xif_memres_if.mem_result.id;
                    assign unit_xif.mem_result.rdata = xif_memres_if.mem_result.rdata;
                    assign unit_xif.mem_result.err   = xif_memres_if.mem_result.err;
                    assign unit_xif.mem_result.dbg   = xif_memres_if.mem_result.dbg;
                    assign trans_complete_valid_o    = trans_complete_valid;
                    assign trans_complete_id_o       = trans_complete_id;
                    assign trans_complete_exc_o      = trans_complete_exc;
                    assign trans_complete_exccode_o  = trans_complete_exccode;
                end
                if (op_unit'(i) == UNIT_ELEM) begin
                    assign xreg_valid_o = xreg_valid;
                    assign xreg_id_o    = xreg_id;
                    assign xreg_addr_o  = xreg_addr;
                    assign xreg_data_o  = xreg_data;
                end
            end
        end
    endgenerate

    // TODO keep track of currently active unit and use that until the last cycle is signaled
    always_comb begin
        pipe_out_valid_o          = '0;
        pipe_out_instr_id_o       =          DONT_CARE_ZERO ?             '0  :             'x   ;
        pipe_out_eew_o            =          DONT_CARE_ZERO ? cfg_vsew'  ('0) : cfg_vsew'  ('x)  ;
        pipe_out_vaddr_o          =          DONT_CARE_ZERO ?             '0  :             'x   ;
        pipe_out_res_store_o      =          DONT_CARE_ZERO ?             '0  :             'x   ;
        pipe_out_res_valid_o      =          DONT_CARE_ZERO ?             '0  :             'x   ;
        pipe_out_res_flags_o      = {RES_CNT{DONT_CARE_ZERO ? pack_flags'('0) : pack_flags'('x)}};
        pipe_out_res_data_o       =          DONT_CARE_ZERO ?             '0  :             'x   ;
        pipe_out_res_mask_o       =          DONT_CARE_ZERO ?             '0  :             'x   ;
        pipe_out_pend_clear_o     =          DONT_CARE_ZERO ?             '0  :             'x   ;
        pipe_out_pend_clear_cnt_o =          DONT_CARE_ZERO ?             '0  :             'x   ;
        for (int i = 0; i < UNIT_CNT; i++) begin
            if (UNITS[i] & unit_out_valid[i]) begin
                pipe_out_valid_o          = 1'b1;
                pipe_out_instr_id_o       = unit_out_instr_id      [i];
                pipe_out_eew_o            = unit_out_eew           [i];
                pipe_out_vaddr_o          = unit_out_vaddr         [i];
                pipe_out_res_store_o      = unit_out_res_store     [i];
                pipe_out_res_valid_o      = unit_out_res_valid     [i];
                pipe_out_res_flags_o      = unit_out_res_flags     [i];
                pipe_out_res_data_o       = unit_out_res_data      [i];
                pipe_out_res_mask_o       = unit_out_res_mask      [i];
                pipe_out_pend_clear_o     = unit_out_pend_clear    [i];
                pipe_out_pend_clear_cnt_o = unit_out_pend_clear_cnt[i];
            end
        end
        // TODO remove below code
        unit_out_ready = {UNIT_CNT{pipe_out_ready_i}};
    end

endmodule
