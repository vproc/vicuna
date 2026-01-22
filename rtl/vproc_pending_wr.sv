// Copyright TU Wien
// Licensed under the Solderpad Hardware License v2.1, see LICENSE.txt for details
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1


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
        if (unit_i == UNIT_LSU) begin
            unique case ({emul_i, mode_i.lsu.nfields})
                {EMUL_1, 3'b000}: pend_vd = 32'h01 <<  rd_i.addr              ;
                {EMUL_1, 3'b001}: pend_vd = 32'h03 <<  rd_i.addr              ;
                {EMUL_1, 3'b010}: pend_vd = 32'h07 <<  rd_i.addr              ;
                {EMUL_1, 3'b011}: pend_vd = 32'h0F <<  rd_i.addr              ;
                {EMUL_1, 3'b100}: pend_vd = 32'h1F <<  rd_i.addr              ;
                {EMUL_1, 3'b101}: pend_vd = 32'h3F <<  rd_i.addr              ;
                {EMUL_1, 3'b110}: pend_vd = 32'h7F <<  rd_i.addr              ;
                {EMUL_1, 3'b111}: pend_vd = 32'hFF <<  rd_i.addr              ;
                {EMUL_2, 3'b000}: pend_vd = 32'h03 << {rd_i.addr[4:1], 1'b0  };
                {EMUL_2, 3'b001}: pend_vd = 32'h0F << {rd_i.addr[4:1], 1'b0  };
                {EMUL_2, 3'b010}: pend_vd = 32'h3F << {rd_i.addr[4:1], 1'b0  };
                {EMUL_2, 3'b011}: pend_vd = 32'hFF << {rd_i.addr[4:1], 1'b0  };
                {EMUL_4, 3'b000}: pend_vd = 32'h0F << {rd_i.addr[4:2], 2'b00 };
                {EMUL_4, 3'b001}: pend_vd = 32'hFF << {rd_i.addr[4:2], 2'b00 };
                {EMUL_8, 3'b000}: pend_vd = 32'hFF << {rd_i.addr[4:3], 3'b000};
                default: ;
            endcase
        end else begin
            unique case ({emul_i, widenarrow_i == OP_NARROWING})
                {EMUL_1, 1'b0},
                {EMUL_1, 1'b1},
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
