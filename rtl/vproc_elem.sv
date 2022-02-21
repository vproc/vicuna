// Copyright TU Wien
// Licensed under the Solderpad Hardware License v2.1, see LICENSE.txt for details
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1


module vproc_elem #(
        parameter int unsigned         VREG_W         = 128,  // width in bits of vector registers
        parameter int unsigned         CFG_VL_W       = 7,    // width of VL reg in bits (= log2(VREG_W))
        parameter int unsigned         GATHER_OP_W    = 32,   // ELEM unit GATHER operand width in bits
        parameter bit                  BUF_RESULTS    = 1'b1, // insert pipeline stage after computing result
        parameter type                 CTRL_T         = logic,
        parameter bit                  DONT_CARE_ZERO = 1'b0  // initialize don't care values to zero
    )(
        input  logic                   clk_i,
        input  logic                   async_rst_ni,
        input  logic                   sync_rst_ni,

        input  logic                   pipe_in_valid_i,
        output logic                   pipe_in_ready_o,
        input  CTRL_T                  pipe_in_ctrl_i,
        input  logic [31           :0] pipe_in_op1_i,
        input  logic [31           :0] pipe_in_op2_i,
        input  logic [GATHER_OP_W-1:0] pipe_in_op_gather_i,
        input  logic                   pipe_in_mask_i,

        output logic                   pipe_out_valid_o,
        input  logic                   pipe_out_ready_i,
        output CTRL_T                  pipe_out_ctrl_o,
        output logic                   pipe_out_xreg_valid_o,
        output logic [31           :0] pipe_out_xreg_data_o,
        output logic [4            :0] pipe_out_xreg_addr_o,
        output logic                   pipe_out_res_valid_o,
        output logic [31           :0] pipe_out_res_o,
        output logic [3            :0] pipe_out_mask_o
    );

    import vproc_pkg::*;


    ///////////////////////////////////////////////////////////////////////////
    // ELEM BUFFERS

    localparam int unsigned ELEM_COUNTER_W = $clog2(VREG_W / 8) + 3;
    typedef union packed {
        logic [ELEM_COUNTER_W-1:0] val;
        struct packed {
            logic [2:0]                mul;  // mul part (vreg index)
            logic [ELEM_COUNTER_W-4:0] low;  // counter part in vreg (vreg pos)
        } part;
    } elem_counter;

    logic  state_res_ready;
    logic  state_res_valid_q, state_res_valid_d;
    CTRL_T state_res_q,       state_res_d;

    // operands and result
    logic [31:0] result_q,         result_d;
    logic        result_mask_q,    result_mask_d;
    logic        result_valid_q,   result_valid_d;

    // track whether there are any valid results:
    logic        has_valid_result_q, has_valid_result_d;
    elem_counter vd_count_q,         vd_count_d;
    logic                            vd_store_d;
    logic [4:0]                      vd_vd_d;

    generate
        if (BUF_RESULTS) begin
            always_ff @(posedge clk_i or negedge async_rst_ni) begin : vproc_elem_stage_res_valid
                if (~async_rst_ni) begin
                    state_res_valid_q <= 1'b0;
                end
                else if (~sync_rst_ni) begin
                    state_res_valid_q <= 1'b0;
                end
                else if (state_res_ready) begin
                    state_res_valid_q <= state_res_valid_d;
                end
            end
            always_ff @(posedge clk_i) begin : vproc_elem_stage_res
                if (state_res_ready & state_res_valid_d) begin
                    state_res_q    <= state_res_d;
                    result_q       <= result_d;
                    result_mask_q  <= result_mask_d;
                    result_valid_q <= result_valid_d;
                end
            end
            assign state_res_ready = ~state_res_valid_q | pipe_out_ready_i;
        end else begin
            always_comb begin
                state_res_valid_q = state_res_valid_d;
                state_res_q       = state_res_d;
                result_q          = result_d;
                result_mask_q     = result_mask_d;
                result_valid_q    = result_valid_d;
            end
            assign state_res_ready = pipe_out_ready_i;
        end

        always_ff @(posedge clk_i) begin
            if (pipe_out_ready_i) begin
                vd_count_q         <= vd_count_d;
                has_valid_result_q <= has_valid_result_d;
            end
        end
    endgenerate


    ///////////////////////////////////////////////////////////////////////////
    // ELEM OPERAND AND RESULT CONVERSION

    assign pipe_in_ready_o   = state_res_ready;
    assign state_res_valid_d = pipe_in_valid_i;
    assign state_res_d       = pipe_in_ctrl_i;

    logic [31:0]            elem_q;
    logic                   elem_idx_valid_q;
    logic                   mask_q;
    logic [31:0]            redinit_q;
    logic [GATHER_OP_W-1:0] gather_shift_q;
    logic                   v0msk_q;
    assign elem_q         = pipe_in_op1_i;
    assign mask_q         = pipe_in_op2_i[0];
    assign redinit_q      = pipe_in_op2_i;
    assign gather_shift_q = pipe_in_op_gather_i;
    assign v0msk_q        = pipe_in_mask_i;

    logic [31:0] gather_byte_idx;
    always_comb begin
        gather_byte_idx = DONT_CARE_ZERO ? '0 : 'x;
        unique case (pipe_in_ctrl_i.eew)
            VSEW_8:  gather_byte_idx = {24'b0                               , elem_q[7 :0]       };
            VSEW_16: gather_byte_idx = {15'b0                               , elem_q[15:0], 1'b0 };
            VSEW_32: gather_byte_idx = {elem_q[31] | elem_q[30] | elem_q[29], elem_q[28:0], 2'b00};
            default: ;
        endcase
    end
    always_comb begin
        elem_idx_valid_q = DONT_CARE_ZERO ? '0 : 'x;
        unique case (pipe_in_ctrl_i.emul)
            EMUL_1: elem_idx_valid_q = gather_byte_idx[31:$clog2(VREG_W/8)  ] == '0;
            EMUL_2: elem_idx_valid_q = gather_byte_idx[31:$clog2(VREG_W/8)+1] == '0;
            EMUL_4: elem_idx_valid_q = gather_byte_idx[31:$clog2(VREG_W/8)+2] == '0;
            EMUL_8: elem_idx_valid_q = gather_byte_idx[31:$clog2(VREG_W/8)+3] == '0;
            default: ;
        endcase
    end

    // XREG write-back
    assign pipe_out_xreg_valid_o = state_res_q.mode.elem.xreg & ((state_res_q.mode.elem.op == ELEM_XMV) ? state_res_q.first_cycle : state_res_q.last_cycle);
    assign pipe_out_xreg_data_o  = result_q;
    assign pipe_out_xreg_addr_o  = state_res_q.vd;

    // track whether there are any valid results
    always_comb begin
        has_valid_result_d = has_valid_result_q;
        if (state_res_q.first_cycle) begin
            has_valid_result_d = 1'b0;
        end
        if (result_valid_q) begin
            has_valid_result_d = 1'b1;
        end
    end

    // determine when we see the first valid result
    logic first_valid_result;
    assign first_valid_result = result_valid_q & (state_res_q.first_cycle | ~has_valid_result_q);

    always_comb begin
        vd_count_d.val = DONT_CARE_ZERO ? '0 : 'x;
        unique case (state_res_q.eew)
            VSEW_8:  vd_count_d.val = vd_count_q.val + {{(ELEM_COUNTER_W-1){1'b0}}, result_valid_q      };
            VSEW_16: vd_count_d.val = vd_count_q.val + {{(ELEM_COUNTER_W-2){1'b0}}, result_valid_q, 1'b0};
            VSEW_32: vd_count_d.val = vd_count_q.val + {{(ELEM_COUNTER_W-3){1'b0}}, result_valid_q, 2'b0};
            default: ;
        endcase
        if (first_valid_result) begin
            vd_count_d.val      = '0;
            vd_count_d.val[1:0] = DONT_CARE_ZERO ? '0 : 'x;
            unique case (state_res_q.eew)
                VSEW_8:  vd_count_d.val[1:0] = 2'b00;
                VSEW_16: vd_count_d.val[1:0] = 2'b01;
                VSEW_32: vd_count_d.val[1:0] = 2'b11;
                default: ;
            endcase
        end
    end
    assign vd_store_d = ~state_res_q.mode.elem.xreg & result_valid_q & (vd_count_d.part.low == '1);
    always_comb begin
        vd_vd_d = DONT_CARE_ZERO ? '0 : 'x;
        unique case (state_res_q.emul)
            EMUL_1: vd_vd_d = state_res_q.vd;
            EMUL_2: vd_vd_d = state_res_q.vd | {4'b0, vd_count_d.part.mul[0:0]};
            EMUL_4: vd_vd_d = state_res_q.vd | {3'b0, vd_count_d.part.mul[1:0]};
            EMUL_8: vd_vd_d = state_res_q.vd | {2'b0, vd_count_d.part.mul[2:0]};
            default: ;
        endcase
    end

    assign pipe_out_valid_o     = state_res_valid_q;
    always_comb begin
        pipe_out_ctrl_o           = state_res_q;
        pipe_out_ctrl_o.count.val = {1'b0, vd_count_d.val};
        pipe_out_ctrl_o.vd_store  = vd_store_d;
        pipe_out_ctrl_o.vd        = vd_vd_d;
    end
    assign pipe_out_res_valid_o = result_valid_q;
    assign pipe_out_res_o       = result_q;
    assign pipe_out_mask_o      = {4{result_mask_q}};


    ///////////////////////////////////////////////////////////////////////////
    // ELEM OPERATION:

    logic [31:0] counter_q, counter_d;
    logic        counter_inc;
    always_ff @(posedge clk_i) begin
        counter_q <= counter_d;
    end
    assign counter_d = (pipe_in_ctrl_i.first_cycle ? 32'b0 : counter_q) + {31'b0, counter_inc};

    logic        v0msk;
    logic [31:0] reduct_val;
    assign v0msk      = v0msk_q | ~pipe_in_ctrl_i.mode.elem.masked;
    assign reduct_val = pipe_in_ctrl_i.first_cycle ? redinit_q : result_q;
    always_comb begin
        counter_inc    = DONT_CARE_ZERO ? '0 : 'x;
        result_d       = DONT_CARE_ZERO ? '0 : 'x;
        result_mask_d  = DONT_CARE_ZERO ? '0 : 'x;
        result_valid_d = DONT_CARE_ZERO ? '0 : 'x;
        unique case (pipe_in_ctrl_i.mode.elem.op)
            // move from vreg index 0 to xreg with sign extension
            ELEM_XMV: begin
                unique case (pipe_in_ctrl_i.eew)
                    VSEW_8:  result_d = {{24{elem_q[7 ]}}, elem_q[7 :0]};
                    VSEW_16: result_d = {{16{elem_q[15]}}, elem_q[15:0]};
                    VSEW_32: result_d =                    elem_q       ;
                    default: ;
                endcase
            end
            // vid writes each element's index to the destination vreg and can
            // be masked by v0
            ELEM_VID: begin
                counter_inc    = 1'b1;
                result_d       = pipe_in_ctrl_i.first_cycle ? '0 : counter_q;
                result_mask_d  = ~pipe_in_ctrl_i.vl_part_0 & v0msk;
                result_valid_d = 1'b1;
            end
            // vpopc and viota count the number of set bits in a mask vreg;
            // both can be masked by v0, in which case only unmasked elements
            // contribute to the sum and for viota only unmasked elements are
            // written
            ELEM_VPOPC,
            ELEM_VIOTA: begin
                counter_inc    = mask_q & ~pipe_in_ctrl_i.vl_part_0 & v0msk;
                result_d       = pipe_in_ctrl_i.first_cycle ? '0 : counter_q;
                result_mask_d  = ~pipe_in_ctrl_i.vl_part_0 & v0msk;
                result_valid_d = 1'b1;
            end
            // vfirst finds the index of the first set bit in a mask vreg and
            // returns -1 if there is none; can be masked by v0
            ELEM_VFIRST: begin
                counter_inc    = pipe_in_ctrl_i.first_cycle | (result_q[31] & ~mask_q);
                result_d       = pipe_in_ctrl_i.first_cycle ? {32{~mask_q}} : (result_q[31] & ~mask_q) ? '1 : counter_q;
                result_mask_d  = ~pipe_in_ctrl_i.vl_part_0 & v0msk;
                result_valid_d = 1'b1;
            end
            // vcompress packs elements for which the corresponding bit in a
            // mask vreg is set; cannot be masked by v0
            ELEM_VCOMPRESS: begin
                result_d       = elem_q;
                result_mask_d  = ~pipe_in_ctrl_i.vl_part_0;
                result_valid_d = mask_q;
            end
            // vgather gathers elements from a vreg based on indices from a
            // second vreg; can be masked by v0
            ELEM_VRGATHER: begin
                result_d = (pipe_in_ctrl_i.aux_count == '0) ? '0 : result_q;
                //if (pipe_in_ctrl_i.aux_count == elem_q[$clog2(VREG_W/8)-1:$clog2(GATHER_OP_W/8)]) begin
                if (pipe_in_ctrl_i.aux_count == gather_byte_idx[$clog2(VREG_W/8)-1:$clog2(GATHER_OP_W/8)]) begin
                    result_d       = gather_shift_q[{{$clog2(VREG_W/GATHER_OP_W){1'b0}}, gather_byte_idx[$clog2(GATHER_OP_W/8)-1:0] & ({$clog2(GATHER_OP_W/8){1'b1}} << 2)} * 8 +: 32];
                    result_d[15:0] = gather_shift_q[{{$clog2(VREG_W/GATHER_OP_W){1'b0}}, gather_byte_idx[$clog2(GATHER_OP_W/8)-1:0] & ({$clog2(GATHER_OP_W/8){1'b1}} << 1)} * 8 +: 16];
                    result_d[7 :0] = gather_shift_q[{{$clog2(VREG_W/GATHER_OP_W){1'b0}}, gather_byte_idx[$clog2(GATHER_OP_W/8)-1:0] & ({$clog2(GATHER_OP_W/8){1'b1}}     )} * 8 +: 8 ];
                    if (~elem_idx_valid_q) begin
                        result_d = '0;
                    end
                end
                result_mask_d  = ~pipe_in_ctrl_i.vl_part_0 & v0msk;
                result_valid_d = pipe_in_ctrl_i.aux_count == '1;
            end
            // flush the destination register after a vcompress or reduction
            // (note that a flush might potentially write to more registers
            // than are part of the vreg group, but for these the write mask
            // will be all 0s)
            ELEM_FLUSH: begin
                result_mask_d  = 1'b0;
                result_valid_d = 1'b1;
            end

            // reduction operations
            // TODO support masked reductions (currently only unmasked)
            ELEM_VREDSUM: begin
                result_d       = ~pipe_in_ctrl_i.vl_part_0 ? (elem_q + reduct_val) : reduct_val;
                result_mask_d  = ~pipe_in_ctrl_i.vl_0;
                result_valid_d = pipe_in_ctrl_i.last_cycle;
            end
            ELEM_VREDAND: begin
                result_d       = ~pipe_in_ctrl_i.vl_part_0 ? (elem_q & reduct_val) : reduct_val;
                result_mask_d  = ~pipe_in_ctrl_i.vl_0;
                result_valid_d = pipe_in_ctrl_i.last_cycle;
            end
            ELEM_VREDOR: begin
                result_d       = ~pipe_in_ctrl_i.vl_part_0 ? (elem_q | reduct_val) : reduct_val;
                result_mask_d  = ~pipe_in_ctrl_i.vl_0;
                result_valid_d = pipe_in_ctrl_i.last_cycle;
            end
            ELEM_VREDXOR: begin
                result_d       = ~pipe_in_ctrl_i.vl_part_0 ? (elem_q ^ reduct_val) : reduct_val;
                result_mask_d  = ~pipe_in_ctrl_i.vl_0;
                result_valid_d = pipe_in_ctrl_i.last_cycle;
            end
            ELEM_VREDMINU: begin
                result_d = reduct_val;
                if (~pipe_in_ctrl_i.vl_part_0) begin
                    unique case (pipe_in_ctrl_i.eew)
                        VSEW_8:  result_d[7 :0] = (elem_q[7 :0] < reduct_val[7 :0]) ? elem_q[7 :0] : reduct_val[7 :0];
                        VSEW_16: result_d[15:0] = (elem_q[15:0] < reduct_val[15:0]) ? elem_q[15:0] : reduct_val[15:0];
                        VSEW_32: result_d       = (elem_q       < reduct_val      ) ? elem_q       : reduct_val      ;
                        default: ;
                    endcase
                end
                result_mask_d  = ~pipe_in_ctrl_i.vl_0;
                result_valid_d = pipe_in_ctrl_i.last_cycle;
            end
            ELEM_VREDMIN: begin
                result_d = reduct_val;
                if (~pipe_in_ctrl_i.vl_part_0) begin
                    unique case (pipe_in_ctrl_i.eew)
                        VSEW_8:  result_d[7 :0] = ($signed(elem_q[7 :0]) < $signed(reduct_val[7 :0])) ? elem_q[7 :0] : reduct_val[7 :0];
                        VSEW_16: result_d[15:0] = ($signed(elem_q[15:0]) < $signed(reduct_val[15:0])) ? elem_q[15:0] : reduct_val[15:0];
                        VSEW_32: result_d       = ($signed(elem_q      ) < $signed(reduct_val      )) ? elem_q       : reduct_val      ;
                        default: ;
                    endcase
                end
                result_mask_d  = ~pipe_in_ctrl_i.vl_0;
                result_valid_d = pipe_in_ctrl_i.last_cycle;
            end
            ELEM_VREDMAXU: begin
                result_d = reduct_val;
                if (~pipe_in_ctrl_i.vl_part_0) begin
                    unique case (pipe_in_ctrl_i.eew)
                        VSEW_8:  result_d[7 :0] = (elem_q[7 :0] > reduct_val[7 :0]) ? elem_q[7 :0] : reduct_val[7 :0];
                        VSEW_16: result_d[15:0] = (elem_q[15:0] > reduct_val[15:0]) ? elem_q[15:0] : reduct_val[15:0];
                        VSEW_32: result_d       = (elem_q       > reduct_val      ) ? elem_q       : reduct_val      ;
                        default: ;
                    endcase
                end
                result_mask_d  = ~pipe_in_ctrl_i.vl_0;
                result_valid_d = pipe_in_ctrl_i.last_cycle;
            end
            ELEM_VREDMAX: begin
                result_d = reduct_val;
                if (~pipe_in_ctrl_i.vl_part_0) begin
                    unique case (pipe_in_ctrl_i.eew)
                        VSEW_8:  result_d[7 :0] = ($signed(elem_q[7 :0]) > $signed(reduct_val[7 :0])) ? elem_q[7 :0] : reduct_val[7 :0];
                        VSEW_16: result_d[15:0] = ($signed(elem_q[15:0]) > $signed(reduct_val[15:0])) ? elem_q[15:0] : reduct_val[15:0];
                        VSEW_32: result_d       = ($signed(elem_q      ) > $signed(reduct_val      )) ? elem_q       : reduct_val      ;
                        default: ;
                    endcase
                end
                result_mask_d  = ~pipe_in_ctrl_i.vl_0;
                result_valid_d = pipe_in_ctrl_i.last_cycle;
            end
            default: ;

        endcase
    end


endmodule
