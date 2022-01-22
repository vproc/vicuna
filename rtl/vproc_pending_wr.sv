// Copyright TU Wien
// Licensed under the ISC license, see LICENSE.txt for details
// SPDX-License-Identifier: ISC


module vproc_pending_wr #(
        parameter bit                   DONT_CARE_ZERO = 1'b0 // initialize don't care values to zero
    )(
        input  vproc_pkg::cfg_vsew      vsew_i,
        input  vproc_pkg::cfg_emul      emul_i,

        input  vproc_pkg::op_unit       unit_i,
        input  vproc_pkg::op_mode       mode_i,
        input  vproc_pkg::op_widenarrow widenarrow_i,

        input  vproc_pkg::op_regd       rd_i,

        output logic [31:0]             pending_wr_o
    );

    import vproc_pkg::*;

    logic [31:0] pend_vd;
    always_comb begin
        pend_vd = DONT_CARE_ZERO ? '0 : 'x;
        unique case ({emul_i, widenarrow_i == OP_NARROWING})
            {EMUL_1, 1'b0},
            {EMUL_2, 1'b1}: begin
                pend_vd = rd_i.vreg ? (32'h00000001 <<  rd_i.addr              ) : 32'b0;
            end
            {EMUL_2, 1'b0},
            {EMUL_4, 1'b1}: begin
                pend_vd = rd_i.vreg ? (32'h00000003 << {rd_i.addr[4:1], 1'b0  }) : 32'b0;
            end
            {EMUL_4, 1'b0},
            {EMUL_8, 1'b1}: begin
                pend_vd = rd_i.vreg ? (32'h0000000F << {rd_i.addr[4:2], 2'b00 }) : 32'b0;
            end
            {EMUL_8, 1'b0}: begin
                pend_vd = rd_i.vreg ? (32'h000000FF << {rd_i.addr[4:3], 3'b000}) : 32'b0;
            end
            default: ;
        endcase
    end

    always_comb begin
        pending_wr_o = pend_vd;
        unique case (unit_i)
            UNIT_LSU: begin
                if (mode_i.lsu.store) begin
                    pending_wr_o  = '0;
                end
            end
            UNIT_ALU: begin
                if (mode_i.alu.cmp) begin
                    pending_wr_o = rd_i.vreg ? (32'h1 << rd_i.addr) : 32'b0;
                end
            end
            UNIT_ELEM: begin
                if (mode_i.elem.xreg) begin
                    pending_wr_o = '0;
                end
            end
            default: ;
        endcase
    end

endmodule
