// Copyright TU Wien
// Licensed under the Solderpad Hardware License v2.1, see LICENSE.txt for details
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1


module vproc_unit_wrapper import vproc_pkg::*; #(
        parameter op_unit                            UNIT            = UNIT_ALU,
        parameter int unsigned                       XIF_ID_W        = 3,
        parameter int unsigned                       XIF_ID_CNT      = 8,
        parameter int unsigned                       VREG_W          = 128,
        parameter int unsigned                       OP_CNT          = 2,
        parameter int unsigned                       MAX_OP_W        = 32,
        parameter int unsigned                       RES_CNT         = 2,
        parameter int unsigned                       MAX_RES_W       = 32,
        parameter int unsigned                       VLSU_QUEUE_SZ   = 4,
        parameter bit [VLSU_FLAGS_W-1:0]             VLSU_FLAGS      = '0,
        parameter mul_type                           MUL_TYPE        = MUL_GENERIC,
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
        output cfg_vsew                              pipe_out_eew_o,
        output logic    [4:0]                        pipe_out_vaddr_o,
        output logic    [RES_CNT-1:0]                pipe_out_res_store_o,
        output logic    [RES_CNT-1:0]                pipe_out_res_valid_o,
        output pack_flags            [RES_CNT  -1:0] pipe_out_res_flags_o,
        output logic    [RES_CNT-1:0][MAX_RES_W-1:0] pipe_out_res_data_o,
        output logic    [RES_CNT-1:0][MAX_RES_W-1:0] pipe_out_res_mask_o,
        output logic                                 pipe_out_pend_clear_o,
        output logic    [1:0]                        pipe_out_pend_clear_cnt_o,
        output logic                                 pipe_out_instr_done_o,

        output logic                                 pending_load_o,
        output logic                                 pending_store_o,

        input  logic    [31:0]                       vreg_pend_rd_i,

        input  instr_state [XIF_ID_CNT         -1:0] instr_state_i,

        vproc_xif.coproc_mem                         xif_mem_if,
        vproc_xif.coproc_mem_result                  xif_memres_if,

        output logic                                 trans_complete_valid_o,
        input  logic                                 trans_complete_ready_i,
        output logic    [XIF_ID_W              -1:0] trans_complete_id_o,
        output logic                                 trans_complete_exc_o,
        output logic    [5:0]                        trans_complete_exccode_o,

        output logic                                 xreg_valid_o,
        input  logic                                 xreg_ready_i,
        output logic    [XIF_ID_W              -1:0] xreg_id_o,
        output logic    [4:0]                        xreg_addr_o,
        output logic    [31:0]                       xreg_data_o
    );

    generate
        if (UNIT == UNIT_LSU) begin
            CTRL_T                 unit_out_ctrl;
            logic [MAX_OP_W  -1:0] unit_out_res;
            logic [MAX_OP_W/8-1:0] unit_out_mask;
            vproc_lsu #(
                .VMEM_W                   ( MAX_OP_W                                    ),
                .CTRL_T                   ( CTRL_T                                      ),
                .XIF_ID_W                 ( XIF_ID_W                                    ),
                .XIF_ID_CNT               ( XIF_ID_CNT                                  ),
                .VLSU_QUEUE_SZ            ( VLSU_QUEUE_SZ                               ),
                .VLSU_FLAGS               ( VLSU_FLAGS                                  ),
                .DONT_CARE_ZERO           ( DONT_CARE_ZERO                              )
            ) lsu (
                .clk_i                    ( clk_i                                       ),
                .async_rst_ni             ( async_rst_ni                                ),
                .sync_rst_ni              ( sync_rst_ni                                 ),
                .pipe_in_valid_i          ( pipe_in_valid_i                             ),
                .pipe_in_ready_o          ( pipe_in_ready_o                             ),
                .pipe_in_ctrl_i           ( pipe_in_ctrl_i                              ),
                .pipe_in_op1_i            ( pipe_in_op_data_i[0][31:0]                  ),
                .pipe_in_op2_i            ( pipe_in_op_data_i[1]                        ),
                .pipe_in_mask_i           ( pipe_in_op_data_i[OP_CNT-1][MAX_OP_W/8-1:0] ),
                .pipe_out_valid_o         ( pipe_out_valid_o                            ),
                .pipe_out_ready_i         ( pipe_out_ready_i                            ),
                .pipe_out_ctrl_o          ( unit_out_ctrl                               ),
                .pipe_out_pend_clr_o      ( pipe_out_pend_clear_o                       ),
                .pipe_out_res_o           ( unit_out_res                                ),
                .pipe_out_mask_o          ( unit_out_mask                               ),
                .pending_load_o           ( pending_load_o                              ),
                .pending_store_o          ( pending_store_o                             ),
                .vreg_pend_rd_i           ( vreg_pend_rd_i                              ),
                .instr_state_i            ( instr_state_i                               ),
                .trans_complete_valid_o   ( trans_complete_valid_o                      ),
                .trans_complete_ready_i   ( trans_complete_ready_i                      ),
                .trans_complete_id_o      ( trans_complete_id_o                         ),
                .trans_complete_exc_o     ( trans_complete_exc_o                        ),
                .trans_complete_exccode_o ( trans_complete_exccode_o                    ),
                .xif_mem_if               ( xif_mem_if                                  ),
                .xif_memres_if            ( xif_memres_if                               )
            );
            always_comb begin
                pipe_out_instr_id_o = unit_out_ctrl.id;
                pipe_out_eew_o      = unit_out_ctrl.eew;
                pipe_out_vaddr_o    = unit_out_ctrl.res_vaddr;
                pipe_out_res_store_o = '0;
                pipe_out_res_valid_o = '0;
                pipe_out_res_flags_o = '{default: pack_flags'('0)};
                pipe_out_res_data_o  = '0;
                pipe_out_res_mask_o  = '0;
                pipe_out_res_flags_o[0].shift           = unit_out_ctrl.res_shift;
                pipe_out_res_flags_o[0].elemwise        = unit_out_ctrl.mode.lsu.stride != LSU_UNITSTRIDE;
                pipe_out_res_store_o[0]                 = unit_out_ctrl.res_store;
                pipe_out_res_valid_o[0]                 = pipe_out_valid_o;
                pipe_out_res_data_o [0]                 = unit_out_res;
                pipe_out_res_mask_o [0][MAX_OP_W/8-1:0] = unit_out_mask;
            end
            assign pipe_out_pend_clear_cnt_o = '0;
            assign pipe_out_instr_done_o     = unit_out_ctrl.last_cycle;
        end
        else if (UNIT == UNIT_ALU) begin
            CTRL_T                 unit_out_ctrl;
            logic [MAX_OP_W  -1:0] unit_out_res_alu;
            logic [MAX_OP_W/8-1:0] unit_out_res_cmp;
            logic [MAX_OP_W/8-1:0] unit_out_mask;
            vproc_alu #(
                .ALU_OP_W           ( MAX_OP_W                                    ),
                .CTRL_T             ( CTRL_T                                      ),
                .DONT_CARE_ZERO     ( DONT_CARE_ZERO                              )
            ) alu (
                .clk_i              ( clk_i                                       ),
                .async_rst_ni       ( async_rst_ni                                ),
                .sync_rst_ni        ( sync_rst_ni                                 ),
                .pipe_in_valid_i    ( pipe_in_valid_i                             ),
                .pipe_in_ready_o    ( pipe_in_ready_o                             ),
                .pipe_in_ctrl_i     ( pipe_in_ctrl_i                              ),
                .pipe_in_op1_i      ( pipe_in_op_data_i[1]                        ),
                .pipe_in_op2_i      ( pipe_in_op_data_i[0]                        ),
                .pipe_in_mask_i     ( pipe_in_op_data_i[OP_CNT-1][MAX_OP_W/8-1:0] ),
                .pipe_out_valid_o   ( pipe_out_valid_o                            ),
                .pipe_out_ready_i   ( pipe_out_ready_i                            ),
                .pipe_out_ctrl_o    ( unit_out_ctrl                               ),
                .pipe_out_res_alu_o ( unit_out_res_alu                            ),
                .pipe_out_res_cmp_o ( unit_out_res_cmp                            ),
                .pipe_out_mask_o    ( unit_out_mask                               )
            );
            always_comb begin
                pipe_out_instr_id_o = unit_out_ctrl.id;
                pipe_out_eew_o      = unit_out_ctrl.eew;
                pipe_out_vaddr_o    = unit_out_ctrl.res_vaddr;
                pipe_out_res_store_o = '0;
                pipe_out_res_valid_o = '0;
                pipe_out_res_flags_o = '{default: pack_flags'('0)};
                pipe_out_res_data_o  = '0;
                pipe_out_res_mask_o  = '0;

                pipe_out_res_store_o[0]                 = unit_out_ctrl.res_store & ~unit_out_ctrl.mode.alu.cmp;
                pipe_out_res_flags_o[0].shift           = unit_out_ctrl.res_shift;
                pipe_out_res_flags_o[0].narrow          = unit_out_ctrl.res_narrow[0];
                pipe_out_res_flags_o[0].saturate        = unit_out_ctrl.mode.alu.sat_res;
                pipe_out_res_flags_o[0].sig             = unit_out_ctrl.mode.alu.sigext;
                pipe_out_res_valid_o[0]                 = pipe_out_valid_o;
                pipe_out_res_data_o [0]                 = unit_out_res_alu;
                pipe_out_res_mask_o [0][MAX_OP_W/8-1:0] = unit_out_mask;

                pipe_out_res_flags_o[1].mul_idx         = unit_out_ctrl.count_mul;
                pipe_out_res_store_o[1]                 = unit_out_ctrl.res_store & unit_out_ctrl.mode.alu.cmp;
                pipe_out_res_valid_o[1]                 = pipe_out_valid_o;
                pipe_out_res_data_o [1][MAX_OP_W/8-1:0] = unit_out_res_cmp;
                pipe_out_res_mask_o [1][MAX_OP_W/8-1:0] = unit_out_mask;
            end
            assign pipe_out_pend_clear_o     = unit_out_ctrl.mode.alu.cmp ? unit_out_ctrl.last_cycle : unit_out_ctrl.res_store;
            assign pipe_out_pend_clear_cnt_o = '0;
            assign pipe_out_instr_done_o     = unit_out_ctrl.last_cycle;
        end
        else if (UNIT == UNIT_MUL) begin
            CTRL_T                 unit_out_ctrl;
            logic [MAX_OP_W  -1:0] unit_out_res;
            logic [MAX_OP_W/8-1:0] unit_out_mask;
            vproc_mul #(
                .MUL_OP_W         ( MAX_OP_W                                    ),
                .MUL_TYPE         ( MUL_TYPE                                    ),
                .CTRL_T           ( CTRL_T                                      ),
                .DONT_CARE_ZERO   ( DONT_CARE_ZERO                              )
            ) mul (
                .clk_i            ( clk_i                                       ),
                .async_rst_ni     ( async_rst_ni                                ),
                .sync_rst_ni      ( sync_rst_ni                                 ),
                .pipe_in_valid_i  ( pipe_in_valid_i                             ),
                .pipe_in_ready_o  ( pipe_in_ready_o                             ),
                .pipe_in_ctrl_i   ( pipe_in_ctrl_i                              ),
                .pipe_in_op1_i    ( pipe_in_op_data_i[1]                        ),
                .pipe_in_op2_i    ( pipe_in_op_data_i[0]                        ),
                .pipe_in_op3_i    ( pipe_in_op_data_i[2]                        ),
                .pipe_in_mask_i   ( pipe_in_op_data_i[OP_CNT-1][MAX_OP_W/8-1:0] ),
                .pipe_out_valid_o ( pipe_out_valid_o                            ),
                .pipe_out_ready_i ( pipe_out_ready_i                            ),
                .pipe_out_ctrl_o  ( unit_out_ctrl                               ),
                .pipe_out_res_o   ( unit_out_res                                ),
                .pipe_out_mask_o  ( unit_out_mask                               )
            );
            always_comb begin
                pipe_out_instr_id_o = unit_out_ctrl.id;
                pipe_out_eew_o      = unit_out_ctrl.eew;
                pipe_out_vaddr_o    = unit_out_ctrl.res_vaddr;
                pipe_out_res_store_o = '0;
                pipe_out_res_valid_o = '0;
                pipe_out_res_flags_o = '{default: pack_flags'('0)};
                pipe_out_res_data_o  = '0;
                pipe_out_res_mask_o  = '0;
                pipe_out_res_flags_o[0].shift           = 1'b1;
                pipe_out_res_store_o[0]                 = unit_out_ctrl.res_store;
                pipe_out_res_valid_o[0]                 = pipe_out_valid_o;
                pipe_out_res_data_o [0]                 = unit_out_res;
                pipe_out_res_mask_o [0][MAX_OP_W/8-1:0] = unit_out_mask;
            end
            assign pipe_out_pend_clear_o     = unit_out_ctrl.res_store;
            assign pipe_out_pend_clear_cnt_o = '0;
            assign pipe_out_instr_done_o     = unit_out_ctrl.last_cycle;
        end
        else if (UNIT == UNIT_SLD) begin
            CTRL_T                 unit_out_ctrl;
            logic [MAX_OP_W  -1:0] unit_out_res;
            logic [MAX_OP_W/8-1:0] unit_out_mask;
            vproc_sld #(
                .SLD_OP_W         ( MAX_OP_W                                    ),
                .CTRL_T           ( CTRL_T                                      ),
                .DONT_CARE_ZERO   ( DONT_CARE_ZERO                              )
            ) sld (
                .clk_i            ( clk_i                                       ),
                .async_rst_ni     ( async_rst_ni                                ),
                .sync_rst_ni      ( sync_rst_ni                                 ),
                .pipe_in_valid_i  ( pipe_in_valid_i                             ),
                .pipe_in_ready_o  ( pipe_in_ready_o                             ),
                .pipe_in_ctrl_i   ( pipe_in_ctrl_i                              ),
                .pipe_in_op_i     ( pipe_in_op_data_i[0]                        ),
                .pipe_in_mask_i   ( pipe_in_op_data_i[OP_CNT-1][MAX_OP_W/8-1:0] ),
                .pipe_out_valid_o ( pipe_out_valid_o                            ),
                .pipe_out_ready_i ( pipe_out_ready_i                            ),
                .pipe_out_ctrl_o  ( unit_out_ctrl                               ),
                .pipe_out_res_o   ( unit_out_res                                ),
                .pipe_out_mask_o  ( unit_out_mask                               )
            );
            always_comb begin
                pipe_out_instr_id_o = unit_out_ctrl.id;
                pipe_out_eew_o      = unit_out_ctrl.eew;
                pipe_out_vaddr_o    = unit_out_ctrl.res_vaddr;
                pipe_out_res_store_o = '0;
                pipe_out_res_valid_o = '0;
                pipe_out_res_flags_o = '{default: pack_flags'('0)};
                pipe_out_res_data_o  = '0;
                pipe_out_res_mask_o  = '0;
                pipe_out_res_flags_o[0].shift           = 1'b1;
                pipe_out_res_store_o[0]                 = unit_out_ctrl.res_store;
                pipe_out_res_valid_o[0]                 = pipe_out_valid_o;
                pipe_out_res_data_o [0]                 = unit_out_res;
                pipe_out_res_mask_o [0][MAX_OP_W/8-1:0] = unit_out_mask;
            end
            assign pipe_out_pend_clear_o     = unit_out_ctrl.res_store;
            assign pipe_out_pend_clear_cnt_o = '0;
            assign pipe_out_instr_done_o     = unit_out_ctrl.last_cycle;
        end
        else if (UNIT == UNIT_ELEM) begin
            logic        unit_out_valid;
            logic        unit_out_ready;
            CTRL_T       unit_out_ctrl;
            logic        unit_out_xreg_valid;
            logic        unit_out_stall;
            logic        unit_out_res_valid;
            logic [31:0] unit_out_res;
            logic [3 :0] unit_out_mask;
            vproc_elem #(
                .VREG_W                ( VREG_W                         ),
                .GATHER_OP_W           ( MAX_OP_W                       ),
                .CTRL_T                ( CTRL_T                         ),
                .DONT_CARE_ZERO        ( DONT_CARE_ZERO                 )
            ) elem (
                .clk_i                 ( clk_i                          ),
                .async_rst_ni          ( async_rst_ni                   ),
                .sync_rst_ni           ( sync_rst_ni                    ),
                .pipe_in_valid_i       ( pipe_in_valid_i                ),
                .pipe_in_ready_o       ( pipe_in_ready_o                ),
                .pipe_in_ctrl_i        ( pipe_in_ctrl_i                 ),
                .pipe_in_op1_i         ( pipe_in_op_data_i[0][31:0]     ),
                .pipe_in_op2_i         ( pipe_in_op_data_i[1][31:0]     ),
                .pipe_in_op2_mask_i    ( pipe_in_op_data_i[OP_CNT-2][0] ),
                .pipe_in_op_gather_i   ( pipe_in_op_data_i[OP_CNT-3]    ),
                .pipe_in_mask_i        ( pipe_in_op_data_i[OP_CNT-1][0] ),
                .pipe_out_valid_o      ( unit_out_valid                 ),
                .pipe_out_ready_i      ( unit_out_ready                 ),
                .pipe_out_ctrl_o       ( unit_out_ctrl                  ),
                .pipe_out_xreg_valid_o ( unit_out_xreg_valid            ),
                .pipe_out_xreg_data_o  ( xreg_data_o                    ),
                .pipe_out_xreg_addr_o  ( xreg_addr_o                    ),
                .pipe_out_res_valid_o  ( unit_out_res_valid             ),
                .pipe_out_res_o        ( unit_out_res                   ),
                .pipe_out_mask_o       ( unit_out_mask                  )
            );
            // guard ELEM unit's pipe_out_res_valid_o with its pipe_out_valid_o
            logic res_valid;
            assign res_valid = unit_out_valid & unit_out_res_valid;
            // ELEM unit's output buffer signals
            logic                has_valid_result_q, has_valid_result_d;
            COUNTER_T            vd_count_q,         vd_count_d;
            COUNTER_T            vs_count_q,         vs_count_d;
            logic                flushing_q,         flushing_d;
            logic [XIF_ID_W-1:0] flushing_id_q,      flushing_id_d;
            vproc_pkg::cfg_vsew  flushing_eew_q,     flushing_eew_d;
            vproc_pkg::cfg_emul  flushing_emul_q,    flushing_emul_d;
            logic [4:0]          flushing_vaddr_q,   flushing_vaddr_d;
            // flush the downstream part of the pipeline after the last cycle if needed
            logic                flush_finished_d, flush_finished_q;
            // Symbolizes when we finish the compress operation and starts the flush process in vcompress
            logic                compress_last_cycle;
            always_ff @(posedge clk_i) begin
                if (pipe_out_ready_i) begin
                    vd_count_q         <= vd_count_d;
                    vs_count_q         <= vs_count_d;
                    has_valid_result_q <= has_valid_result_d;
                    flushing_id_q      <= flushing_id_d;
                    flushing_eew_q     <= flushing_eew_d;
                    flushing_emul_q    <= flushing_emul_d;
                    flushing_vaddr_q   <= flushing_vaddr_d;
                    flush_finished_q   <= flush_finished_d;
                end
            end
            always_ff @(posedge clk_i or negedge async_rst_ni) begin
                if (~async_rst_ni) begin
                    flushing_q <= 1'b0;
                end
                else if (~sync_rst_ni) begin
                    flushing_q <= 1'b0;
                end
                else if (pipe_out_ready_i) begin
                    flushing_q <= flushing_d;
                end
            end
            // track whether there are any valid results
            always_comb begin
                has_valid_result_d = has_valid_result_q;
                if (unit_out_ctrl.first_cycle) begin
                    has_valid_result_d = 1'b0;
                end
                if (res_valid) begin
                    has_valid_result_d = 1'b1;
                end
            end
            // determine when we see the first valid result
            logic first_valid_result;
            assign first_valid_result = ~flushing_q & res_valid & (unit_out_ctrl.first_cycle | ~has_valid_result_q);
            always_comb begin
                vd_count_d.val = DONT_CARE_ZERO ? '0 : 'x;
                vs_count_d.val = DONT_CARE_ZERO ? '0 : 'x;
                unique case (flushing_q ? flushing_eew_q : unit_out_ctrl.eew)
                    VSEW_8:  vd_count_d.val = vd_count_q.val + {{(COUNTER_W-1){1'b0}}, flushing_q | res_valid      };
                    VSEW_16: vd_count_d.val = vd_count_q.val + {{(COUNTER_W-2){1'b0}}, flushing_q | res_valid, 1'b0};
                    VSEW_32: vd_count_d.val = vd_count_q.val + {{(COUNTER_W-3){1'b0}}, flushing_q | res_valid, 2'b0};
                    default: ;
                endcase
                if (first_valid_result) begin
                    vd_count_d.val      = '0;
                    vd_count_d.val[1:0] = DONT_CARE_ZERO ? '0 : 'x;
                    unique case (unit_out_ctrl.eew)
                        VSEW_8:  vd_count_d.val[1:0] = 2'b00;
                        VSEW_16: vd_count_d.val[1:0] = 2'b01;
                        VSEW_32: vd_count_d.val[1:0] = 2'b11;
                        default: ;
                    endcase
                end
                unique case (unit_out_ctrl.eew)
                    VSEW_8:  vs_count_d.val = vs_count_q.val + {{(COUNTER_W-1){1'b0}}, ~flushing_q & unit_out_valid      };
                    VSEW_16: vs_count_d.val = vs_count_q.val + {{(COUNTER_W-2){1'b0}}, ~flushing_q & unit_out_valid, 1'b0};
                    VSEW_32: vs_count_d.val = vs_count_q.val + {{(COUNTER_W-3){1'b0}}, ~flushing_q & unit_out_valid, 2'b0};
                    default: ;
                endcase
                if (unit_out_ctrl.first_cycle) begin
                    vs_count_d.val      = '0;
                    vs_count_d.val[1:0] = DONT_CARE_ZERO ? '0 : 'x;
                    unique case (unit_out_ctrl.eew)
                        VSEW_8:  vs_count_d.val[1:0] = 2'b00;
                        VSEW_16: vs_count_d.val[1:0] = 2'b01;
                        VSEW_32: vs_count_d.val[1:0] = 2'b11;
                        default: ;
                    endcase
                end
            end

            logic instr_speculative, instr_committed;
            always_comb begin
                instr_speculative = DONT_CARE_ZERO ? '0 : 'x;
                instr_committed   = DONT_CARE_ZERO ? '0 : 'x;
                unique case (instr_state_i[unit_out_ctrl.id])
                    INSTR_SPECULATIVE: instr_speculative = 1'b1;
                    INSTR_COMMITTED,
                    INSTR_KILLED:      instr_speculative = 1'b0;
                    default: ;
                endcase
                unique case (instr_state_i[unit_out_ctrl.id])
                    INSTR_SPECULATIVE,
                    INSTR_KILLED:      instr_committed = 1'b0;
                    INSTR_COMMITTED:   instr_committed = 1'b1;
                    default: ;
                endcase
            end

            always_comb begin
                compress_last_cycle = 1'b0;
                unique case (unit_out_ctrl.eew)
                    VSEW_8:  compress_last_cycle = vs_count_d.val[COUNTER_W-5:0] == '1;
                    VSEW_16: compress_last_cycle = vs_count_d.val[COUNTER_W-5:1] == '1;
                    VSEW_32: compress_last_cycle = vs_count_d.val[COUNTER_W-5:2] == '1;
                    default: ;
                endcase
                unique case (unit_out_ctrl.emul)
                    EMUL_2: compress_last_cycle &= vs_count_d.part.mul[  0] == '1;
                    EMUL_4: compress_last_cycle &= vs_count_d.part.mul[1:0] == '1;
                    EMUL_8: compress_last_cycle &= vs_count_d.part.mul[2:0] == '1;
                    default: ;
                endcase
                // We're flushing, so no compress more
                if (flushing_q) begin
                    compress_last_cycle = 1'b0;
                end
            end

            assign unit_out_stall = unit_out_xreg_valid & (instr_speculative | ~xreg_ready_i);

            always_comb begin
                flushing_d          = flushing_q;
                flushing_id_d       = flushing_id_q;
                flushing_eew_d      = flushing_eew_q;
                flushing_emul_d     = flushing_emul_q;
                flushing_vaddr_d    = flushing_vaddr_q;
                flush_finished_d    = flush_finished_q;
                if (~flushing_q & ~flush_finished_d & unit_out_valid & compress_last_cycle & unit_out_ctrl.requires_flush) begin
                    flushing_d       = 1'b1;
                    flushing_id_d    = unit_out_ctrl.id;
                    flushing_eew_d   = unit_out_ctrl.eew;
                    flushing_emul_d  = unit_out_ctrl.emul;
                    flushing_vaddr_d = unit_out_ctrl.res_vaddr;
                end
                if (unit_out_valid & unit_out_ctrl.last_cycle) begin
                    flush_finished_d = 1'b0;
                end
                if (flushing_q & (vd_count_d.part.low == '1)) begin
                    flushing_d          = 1'b0;
                    flush_finished_d    = 1'b1;
                end
            end

            assign xreg_valid_o     = unit_out_valid & unit_out_xreg_valid & instr_committed & ~flushing_q;
            assign xreg_id_o        = unit_out_ctrl.id;
            assign pipe_out_valid_o = (unit_out_valid & ~unit_out_stall) | flushing_q;
            assign unit_out_ready   = pipe_out_ready_i & ~flushing_q & ~unit_out_stall;

            logic [4:0] base_vaddr;
            assign base_vaddr = flushing_q ? flushing_vaddr_q : unit_out_ctrl.res_vaddr;
            logic res_flag_shift_vsew32;
            if (MAX_RES_W > 32) begin
                assign res_flag_shift_vsew32 = vd_count_d.val[$clog2(MAX_RES_W/8)-1:2] == '0;
            end else begin
                assign res_flag_shift_vsew32 = 1'b1;
            end
            always_comb begin
                pipe_out_instr_id_o = flushing_q ? flushing_id_q  : unit_out_ctrl.id;
                pipe_out_eew_o      = flushing_q ? flushing_eew_q : unit_out_ctrl.eew;
                pipe_out_vaddr_o = DONT_CARE_ZERO ? '0 : 'x;
                unique case (flushing_q ? flushing_emul_q : unit_out_ctrl.emul)
                    EMUL_1: pipe_out_vaddr_o = base_vaddr;
                    EMUL_2: pipe_out_vaddr_o = base_vaddr | {4'b0, vd_count_d.part.mul[0:0]};
                    EMUL_4: pipe_out_vaddr_o = base_vaddr | {3'b0, vd_count_d.part.mul[1:0]};
                    EMUL_8: pipe_out_vaddr_o = base_vaddr | {2'b0, vd_count_d.part.mul[2:0]};
                    default: ;
                endcase
                pipe_out_res_store_o = '0;
                pipe_out_res_valid_o = '0;
                pipe_out_res_flags_o = '{default: pack_flags'('0)};
                pipe_out_res_data_o  = '0;
                pipe_out_res_mask_o  = '0;
                pipe_out_res_flags_o[0].shift = DONT_CARE_ZERO ? '0 : 'x;
                unique case (flushing_q ? flushing_eew_q : unit_out_ctrl.eew)
                    VSEW_8:  pipe_out_res_flags_o[0].shift = vd_count_d.val[$clog2(MAX_RES_W/8)-1:0] == '0;
                    VSEW_16: pipe_out_res_flags_o[0].shift = vd_count_d.val[$clog2(MAX_RES_W/8)-1:1] == '0;
                    VSEW_32: pipe_out_res_flags_o[0].shift = res_flag_shift_vsew32;
                    default: ;
                endcase
                pipe_out_res_flags_o[0].elemwise = 1'b1;
                pipe_out_res_flags_o[0].red_op   = unit_out_ctrl.red_op;
                pipe_out_res_store_o[0]          = ((~unit_out_ctrl.mode.elem.xreg & unit_out_res_valid) | flushing_q) & (vd_count_d.part.low == '1 | unit_out_ctrl.red_op);
                pipe_out_res_valid_o[0]          = flushing_q | (unit_out_res_valid & ~flush_finished_q);
                pipe_out_res_data_o [0]          = unit_out_res;
                pipe_out_res_mask_o [0][3:0]     = flushing_q ? '0 : unit_out_mask;
            end
            assign pipe_out_instr_done_o     = unit_out_ctrl.last_cycle; // We only finish after the state being done
            assign pipe_out_pend_clear_o     = (~flushing_q & unit_out_ctrl.last_cycle & ~unit_out_ctrl.requires_flush & ~unit_out_ctrl.mode.elem.xreg) | flush_finished_d;
            assign pipe_out_pend_clear_cnt_o = unit_out_ctrl.emul; // TODO reductions always have destination EMUL == 1
        end
    endgenerate

endmodule
