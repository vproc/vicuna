// Copyright TU Wien
// Licensed under the Solderpad Hardware License v2.1, see LICENSE.txt for details
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1


module vproc_unit_wrapper #(
        parameter vproc_pkg::op_unit                 UNIT            = vproc_pkg::UNIT_ALU,
        parameter int unsigned                       XIF_ID_W        = 3,
        parameter int unsigned                       XIF_ID_CNT      = 8,
        parameter int unsigned                       VREG_W          = 128,
        parameter int unsigned                       OP_CNT          = 2,
        parameter int unsigned                       MAX_OP_W        = 32,
        parameter int unsigned                       RES_CNT         = 2,
        parameter int unsigned                       MAX_RES_W       = 32,
        parameter vproc_pkg::mul_type                MUL_TYPE        = vproc_pkg::MUL_GENERIC,
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

    generate
        if (UNIT == UNIT_LSU) begin
            CTRL_T                 unit_out_ctrl;
            logic [MAX_OP_W  -1:0] unit_out_res;
            logic [MAX_OP_W/8-1:0] unit_out_mask;
            vproc_lsu #(
                .VMEM_W                   ( MAX_OP_W                             ),
                .CTRL_T                   ( CTRL_T                               ),
                .XIF_ID_W                 ( XIF_ID_W                             ),
                .XIF_ID_CNT               ( XIF_ID_CNT                           ),
                .DONT_CARE_ZERO           ( DONT_CARE_ZERO                       )
            ) lsu (
                .clk_i                    ( clk_i                                ),
                .async_rst_ni             ( async_rst_ni                         ),
                .sync_rst_ni              ( sync_rst_ni                          ),
                .pipe_in_valid_i          ( pipe_in_valid_i                      ),
                .pipe_in_ready_o          ( pipe_in_ready_o                      ),
                .pipe_in_ctrl_i           ( pipe_in_ctrl_i                       ),
                .pipe_in_op1_i            ( pipe_in_op_data_i[0][31:0]           ),
                .pipe_in_op2_i            ( pipe_in_op_data_i[1]                 ),
                .pipe_in_mask_i           ( pipe_in_op_data_i[2][MAX_OP_W/8-1:0] ),
                .pipe_out_valid_o         ( pipe_out_valid_o                     ),
                .pipe_out_ready_i         ( 1'b1                                 ),
                .pipe_out_ctrl_o          ( unit_out_ctrl                        ),
                .pipe_out_pend_clr_o      ( pipe_out_pend_clear_o                ),
                .pipe_out_res_o           ( unit_out_res                         ),
                .pipe_out_mask_o          ( unit_out_mask                        ),
                .pending_load_o           ( pending_load_o                       ),
                .pending_store_o          ( pending_store_o                      ),
                .vreg_pend_rd_i           ( vreg_pend_rd_i                       ),
                .instr_spec_i             ( instr_spec_i                         ),
                .instr_killed_i           ( instr_killed_i                       ),
                .instr_done_valid_o       ( instr_done_valid_o                   ),
                .instr_done_id_o          ( instr_done_id_o                      ),
                .trans_complete_valid_o   ( trans_complete_valid_o               ),
                .trans_complete_id_o      ( trans_complete_id_o                  ),
                .trans_complete_exc_o     ( trans_complete_exc_o                 ),
                .trans_complete_exccode_o ( trans_complete_exccode_o             ),
                .xif_mem_if               ( xif_mem_if                           ),
                .xif_memres_if            ( xif_memres_if                        )
            );
            always_comb begin
                pipe_out_instr_id_o = unit_out_ctrl.id;
                pipe_out_eew_o      = unit_out_ctrl.eew;
                pipe_out_vaddr_o    = unit_out_ctrl.res_vaddr;
                pipe_out_res_data_o = '0;
                pipe_out_res_mask_o = '0;
                pipe_out_res_flags_o[0]                 = pack_flags'('0);
                pipe_out_res_flags_o[0].shift           = unit_out_ctrl.res_shift;
                pipe_out_res_flags_o[0].elemwise        = unit_out_ctrl.mode.lsu.stride != LSU_UNITSTRIDE;
                pipe_out_res_store_o[0]                 = unit_out_ctrl.res_store;
                pipe_out_res_valid_o[0]                 = pipe_out_valid_o;
                pipe_out_res_data_o [0]                 = unit_out_res;
                pipe_out_res_mask_o [0][MAX_OP_W/8-1:0] = unit_out_mask;
            end
            assign pipe_out_pend_clear_cnt_o = '0;
            assign pipe_out_instr_done_o = unit_out_ctrl.last_cycle;
        end
        else if (UNIT == UNIT_ALU) begin
            CTRL_T                 unit_out_ctrl;
            logic [MAX_OP_W  -1:0] unit_out_res_alu;
            logic [MAX_OP_W/8-1:0] unit_out_res_cmp;
            logic [MAX_OP_W/8-1:0] unit_out_mask;
            vproc_alu #(
                .ALU_OP_W           ( MAX_OP_W                             ),
                .CTRL_T             ( CTRL_T                               ),
                .DONT_CARE_ZERO     ( DONT_CARE_ZERO                       )
            ) alu (
                .clk_i              ( clk_i                                ),
                .async_rst_ni       ( async_rst_ni                         ),
                .sync_rst_ni        ( sync_rst_ni                          ),
                .pipe_in_valid_i    ( pipe_in_valid_i                      ),
                .pipe_in_ready_o    ( pipe_in_ready_o                      ),
                .pipe_in_ctrl_i     ( pipe_in_ctrl_i                       ),
                .pipe_in_op1_i      ( pipe_in_op_data_i[0]                 ),
                .pipe_in_op2_i      ( pipe_in_op_data_i[1]                 ),
                .pipe_in_mask_i     ( pipe_in_op_data_i[2][MAX_OP_W/8-1:0] ),
                .pipe_out_valid_o   ( pipe_out_valid_o                     ),
                .pipe_out_ready_i   ( pipe_out_ready_i                     ),
                .pipe_out_ctrl_o    ( unit_out_ctrl                        ),
                .pipe_out_res_alu_o ( unit_out_res_alu                     ),
                .pipe_out_res_cmp_o ( unit_out_res_cmp                     ),
                .pipe_out_mask_o    ( unit_out_mask                        )
            );
            always_comb begin
                pipe_out_instr_id_o = unit_out_ctrl.id;
                pipe_out_eew_o      = unit_out_ctrl.eew;
                pipe_out_vaddr_o    = unit_out_ctrl.res_vaddr;
                pipe_out_res_data_o = '0;
                pipe_out_res_mask_o = '0;

                pipe_out_res_flags_o[0]                 = pack_flags'('0);
                pipe_out_res_store_o[0]                 = unit_out_ctrl.res_store & ~unit_out_ctrl.mode.alu.cmp;
                pipe_out_res_flags_o[0].shift           = unit_out_ctrl.res_shift;
                pipe_out_res_flags_o[0].narrow          = unit_out_ctrl.res_narrow[0];
                pipe_out_res_flags_o[0].saturate        = unit_out_ctrl.mode.alu.sat_res;
                pipe_out_res_flags_o[0].sig             = unit_out_ctrl.mode.alu.sigext;
                pipe_out_res_valid_o[0]                 = pipe_out_valid_o;
                pipe_out_res_data_o [0]                 = unit_out_res_alu;
                pipe_out_res_mask_o [0][MAX_OP_W/8-1:0] = unit_out_mask;

                pipe_out_res_flags_o[1]                 = pack_flags'('0);
                pipe_out_res_flags_o[1].mul_idx         = unit_out_ctrl.count_mul;
                pipe_out_res_store_o[1]                 = unit_out_ctrl.res_store & unit_out_ctrl.mode.alu.cmp;
                pipe_out_res_valid_o[1]                 = pipe_out_valid_o;
                pipe_out_res_data_o [1][MAX_OP_W/8-1:0] = unit_out_res_cmp;
                pipe_out_res_mask_o [1][MAX_OP_W/8-1:0] = unit_out_mask;
            end
            assign pipe_out_pend_clear_o     = unit_out_ctrl.mode.alu.cmp ? unit_out_ctrl.last_cycle : unit_out_ctrl.res_store;
            assign pipe_out_pend_clear_cnt_o = '0;
            assign pipe_out_instr_done_o = unit_out_ctrl.last_cycle;
        end
        else if (UNIT == UNIT_MUL) begin
            CTRL_T                 unit_out_ctrl;
            logic [MAX_OP_W  -1:0] unit_out_res;
            logic [MAX_OP_W/8-1:0] unit_out_mask;
            vproc_mul #(
                .MUL_OP_W         ( MAX_OP_W                             ),
                .MUL_TYPE         ( MUL_TYPE                             ),
                .CTRL_T           ( CTRL_T                               ),
                .DONT_CARE_ZERO   ( DONT_CARE_ZERO                       )
            ) mul (
                .clk_i            ( clk_i                                ),
                .async_rst_ni     ( async_rst_ni                         ),
                .sync_rst_ni      ( sync_rst_ni                          ),
                .pipe_in_valid_i  ( pipe_in_valid_i                      ),
                .pipe_in_ready_o  ( pipe_in_ready_o                      ),
                .pipe_in_ctrl_i   ( pipe_in_ctrl_i                       ),
                .pipe_in_op1_i    ( pipe_in_op_data_i[0]                 ),
                .pipe_in_op2_i    ( pipe_in_op_data_i[1]                 ),
                .pipe_in_op3_i    ( pipe_in_op_data_i[2]                 ),
                .pipe_in_mask_i   ( pipe_in_op_data_i[3][MAX_OP_W/8-1:0] ),
                .pipe_out_valid_o ( pipe_out_valid_o                     ),
                .pipe_out_ready_i ( pipe_out_ready_i                     ),
                .pipe_out_ctrl_o  ( unit_out_ctrl                        ),
                .pipe_out_res_o   ( unit_out_res                         ),
                .pipe_out_mask_o  ( unit_out_mask                        )
            );
            always_comb begin
                pipe_out_instr_id_o = unit_out_ctrl.id;
                pipe_out_eew_o      = unit_out_ctrl.eew;
                pipe_out_vaddr_o    = unit_out_ctrl.res_vaddr;
                pipe_out_res_data_o = '0;
                pipe_out_res_mask_o = '0;
                pipe_out_res_flags_o[0]                 = pack_flags'('0);
                pipe_out_res_store_o[0]                 = unit_out_ctrl.res_store;
                pipe_out_res_valid_o[0]                 = pipe_out_valid_o;
                pipe_out_res_data_o [0]                 = unit_out_res;
                pipe_out_res_mask_o [0][MAX_OP_W/8-1:0] = unit_out_mask;
            end
            assign pipe_out_pend_clear_o     = unit_out_ctrl.res_store;
            assign pipe_out_pend_clear_cnt_o = '0;
            assign pipe_out_instr_done_o = unit_out_ctrl.last_cycle;
        end
        else if (UNIT == UNIT_SLD) begin
            CTRL_T                 unit_out_ctrl;
            logic [MAX_OP_W  -1:0] unit_out_res;
            logic [MAX_OP_W/8-1:0] unit_out_mask;
            vproc_sld #(
                .SLD_OP_W         ( MAX_OP_W                             ),
                .CTRL_T           ( CTRL_T                               ),
                .DONT_CARE_ZERO   ( DONT_CARE_ZERO                       )
            ) sld (
                .clk_i            ( clk_i                                ),
                .async_rst_ni     ( async_rst_ni                         ),
                .sync_rst_ni      ( sync_rst_ni                          ),
                .pipe_in_valid_i  ( pipe_in_valid_i                      ),
                .pipe_in_ready_o  ( pipe_in_ready_o                      ),
                .pipe_in_ctrl_i   ( pipe_in_ctrl_i                       ),
                .pipe_in_op_i     ( pipe_in_op_data_i[0]                 ),
                .pipe_in_mask_i   ( pipe_in_op_data_i[1][MAX_OP_W/8-1:0] ),
                .pipe_out_valid_o ( pipe_out_valid_o                     ),
                .pipe_out_ready_i ( pipe_out_ready_i                     ),
                .pipe_out_ctrl_o  ( unit_out_ctrl                        ),
                .pipe_out_res_o   ( unit_out_res                         ),
                .pipe_out_mask_o  ( unit_out_mask                        )
            );
            always_comb begin
                pipe_out_instr_id_o = unit_out_ctrl.id;
                pipe_out_eew_o      = unit_out_ctrl.eew;
                pipe_out_vaddr_o    = unit_out_ctrl.res_vaddr;
                pipe_out_res_data_o = '0;
                pipe_out_res_mask_o = '0;
                pipe_out_res_flags_o[0]                 = pack_flags'('0);
                pipe_out_res_store_o[0]                 = unit_out_ctrl.res_store;
                pipe_out_res_valid_o[0]                 = pipe_out_valid_o;
                pipe_out_res_data_o [0]                 = unit_out_res;
                pipe_out_res_mask_o [0][MAX_OP_W/8-1:0] = unit_out_mask;
            end
            assign pipe_out_pend_clear_o     = unit_out_ctrl.res_store;
            assign pipe_out_pend_clear_cnt_o = '0;
            assign pipe_out_instr_done_o = unit_out_ctrl.last_cycle;
        end
        else if (UNIT == UNIT_ELEM) begin
            logic        elem_out_valid;
            logic        elem_out_ready;
            CTRL_T       elem_out_ctrl;
            logic        elem_out_xreg_valid;
            CTRL_T       unit_out_ctrl;
            logic        unit_out_stall;
            logic        unit_out_res_valid;
            logic [31:0] unit_out_res;
            logic [3 :0] unit_out_mask;
            vproc_elem #(
                .VREG_W                ( VREG_W                     ),
                .GATHER_OP_W           ( MAX_OP_W                   ),
                .CTRL_T                ( CTRL_T                     ),
                .DONT_CARE_ZERO        ( DONT_CARE_ZERO             )
            ) elem (
                .clk_i                 ( clk_i                      ),
                .async_rst_ni          ( async_rst_ni               ),
                .sync_rst_ni           ( sync_rst_ni                ),
                .pipe_in_valid_i       ( pipe_in_valid_i            ),
                .pipe_in_ready_o       ( pipe_in_ready_o            ),
                .pipe_in_ctrl_i        ( pipe_in_ctrl_i             ),
                .pipe_in_op1_i         ( pipe_in_op_data_i[0][31:0] ),
                .pipe_in_op2_i         ( pipe_in_op_data_i[1][31:0] ),
                .pipe_in_op_gather_i   ( pipe_in_op_data_i[2]       ),
                .pipe_in_mask_i        ( pipe_in_op_data_i[3][0]    ),
                .pipe_out_valid_o      ( elem_out_valid             ),
                .pipe_out_ready_i      ( elem_out_ready             ),
                .pipe_out_ctrl_o       ( elem_out_ctrl              ),
                .pipe_out_xreg_valid_o ( elem_out_xreg_valid        ),
                .pipe_out_xreg_data_o  ( xreg_data_o                ),
                .pipe_out_xreg_addr_o  ( xreg_addr_o                ),
                .pipe_out_res_valid_o  ( unit_out_res_valid         ),
                .pipe_out_res_o        ( unit_out_res               ),
                .pipe_out_mask_o       ( unit_out_mask              )
            );
            logic     has_valid_result_q, has_valid_result_d;
            COUNTER_T vd_count_q,         vd_count_d;
            always_ff @(posedge clk_i) begin
                if (elem_out_ready) begin
                    vd_count_q         <= vd_count_d;
                    has_valid_result_q <= has_valid_result_d;
                end
            end
            // track whether there are any valid results
            always_comb begin
                has_valid_result_d = has_valid_result_q;
                if (elem_out_ctrl.first_cycle) begin
                    has_valid_result_d = 1'b0;
                end
                if (unit_out_res_valid) begin
                    has_valid_result_d = 1'b1;
                end
            end
            // determine when we see the first valid result
            logic first_valid_result;
            assign first_valid_result = unit_out_res_valid & (elem_out_ctrl.first_cycle | ~has_valid_result_q);
            always_comb begin
                vd_count_d.val = DONT_CARE_ZERO ? '0 : 'x;
                unique case (elem_out_ctrl.eew)
                    VSEW_8:  vd_count_d.val = vd_count_q.val + {{(COUNTER_W-1){1'b0}}, unit_out_res_valid      };
                    VSEW_16: vd_count_d.val = vd_count_q.val + {{(COUNTER_W-2){1'b0}}, unit_out_res_valid, 1'b0};
                    VSEW_32: vd_count_d.val = vd_count_q.val + {{(COUNTER_W-3){1'b0}}, unit_out_res_valid, 2'b0};
                    default: ;
                endcase
                if (first_valid_result) begin
                    vd_count_d.val      = '0;
                    vd_count_d.val[1:0] = DONT_CARE_ZERO ? '0 : 'x;
                    unique case (elem_out_ctrl.eew)
                        VSEW_8:  vd_count_d.val[1:0] = 2'b00;
                        VSEW_16: vd_count_d.val[1:0] = 2'b01;
                        VSEW_32: vd_count_d.val[1:0] = 2'b11;
                        default: ;
                    endcase
                end
            end
            always_comb begin
                unit_out_ctrl           = elem_out_ctrl;
                unit_out_ctrl.res_store = ~elem_out_ctrl.mode.elem.xreg & unit_out_res_valid & (vd_count_d.part.low == '1);
                unit_out_ctrl.res_vaddr = DONT_CARE_ZERO ? '0 : 'x;
                unique case (elem_out_ctrl.emul)
                    EMUL_1: unit_out_ctrl.res_vaddr = elem_out_ctrl.res_vaddr;
                    EMUL_2: unit_out_ctrl.res_vaddr = elem_out_ctrl.res_vaddr | {4'b0, vd_count_d.part.mul[0:0]};
                    EMUL_4: unit_out_ctrl.res_vaddr = elem_out_ctrl.res_vaddr | {3'b0, vd_count_d.part.mul[1:0]};
                    EMUL_8: unit_out_ctrl.res_vaddr = elem_out_ctrl.res_vaddr | {2'b0, vd_count_d.part.mul[2:0]};
                    default: ;
                endcase
            end
            assign unit_out_stall =                  elem_out_xreg_valid &                    instr_spec_i  [unit_out_ctrl.id];
            assign xreg_valid_o   = elem_out_valid & elem_out_xreg_valid & ~unit_out_stall & ~instr_killed_i[unit_out_ctrl.id];
            assign xreg_id_o      = unit_out_ctrl.id;
            assign pipe_out_valid_o = elem_out_valid &                       ~unit_out_stall;
            assign elem_out_ready = pipe_out_ready_i &                       ~unit_out_stall;
            always_comb begin
                pipe_out_instr_id_o = unit_out_ctrl.id;
                pipe_out_eew_o      = unit_out_ctrl.eew;
                pipe_out_vaddr_o    = unit_out_ctrl.res_vaddr;
                pipe_out_res_data_o = '0;
                pipe_out_res_mask_o = '0;
                pipe_out_res_flags_o[0]       = pack_flags'('0);
                pipe_out_res_flags_o[0].shift = DONT_CARE_ZERO ? '0 : 'x;
                unique case (unit_out_ctrl.eew)
                    VSEW_8:  pipe_out_res_flags_o[0].shift = vd_count_d.val[1:0] == '0;
                    VSEW_16: pipe_out_res_flags_o[0].shift = vd_count_d.val[1:1] == '0;
                    VSEW_32: pipe_out_res_flags_o[0].shift = 1'b1;
                    default: ;
                endcase
                pipe_out_res_store_o[0]      = unit_out_ctrl.res_store;
                pipe_out_res_valid_o[0]      = unit_out_res_valid;
                pipe_out_res_data_o [0]      = unit_out_res;
                pipe_out_res_mask_o [0][3:0] = unit_out_mask;
            end
            assign pipe_out_pend_clear_o     = unit_out_ctrl.last_cycle & ~unit_out_ctrl.requires_flush & ~unit_out_ctrl.mode.elem.xreg;
            assign pipe_out_pend_clear_cnt_o = unit_out_ctrl.emul; // TODO reductions always have destination EMUL == 1
            assign pipe_out_instr_done_o = unit_out_ctrl.last_cycle & ~unit_out_ctrl.requires_flush;
        end
    endgenerate

endmodule
