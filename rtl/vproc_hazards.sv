// Copyright TU Wien
// Licensed under the ISC license, see LICENSE.txt for details
// SPDX-License-Identifier: ISC


module vproc_hazards #(
        parameter bit                   COMB_INIT_ZERO = 1'b0
    )(
        input  vproc_pkg::cfg_vsew      vsew_i,
        input  vproc_pkg::cfg_lmul      lmul_i,

        input  vproc_pkg::op_unit       unit_i,
        input  vproc_pkg::op_mode       mode_i,
        input  vproc_pkg::op_widenarrow widenarrow_i,

        input  vproc_pkg::op_regs       rs1_i,
        input  vproc_pkg::op_regs       rs2_i,
        input  vproc_pkg::op_regd       rd_i,

        output logic [31:0]             rd_hazards_o,
        output logic [31:0]             wr_hazards_o
    );

    import vproc_pkg::*;

    cfg_emul lsu_emul;
    always_comb begin
        lsu_emul = COMB_INIT_ZERO ? cfg_emul'('0) : cfg_emul'('x);
        unique case ({mode_i.lsu.eew, vsew_i})
            {VSEW_8 , VSEW_32}: begin   // EEW / SEW = 1 / 4
                lsu_emul = (lmul_i == LMUL_8) ? EMUL_2 : EMUL_1;
            end
            {VSEW_8 , VSEW_16},
            {VSEW_16, VSEW_32}: begin   // EEW / SEW = 1 / 2
                lsu_emul = (lmul_i == LMUL_8) ? EMUL_4 : ((lmul_i == LMUL_4) ? EMUL_2 : EMUL_1);
            end
            {VSEW_8 , VSEW_8 },
            {VSEW_16, VSEW_16},
            {VSEW_32, VSEW_32}: begin   // EEW / SEW = 1
                case (lmul_i)
                    LMUL_F8,
                    LMUL_F4,
                    LMUL_F2,
                    LMUL_1:  lsu_emul = EMUL_1;
                    LMUL_2:  lsu_emul = EMUL_2;
                    LMUL_4:  lsu_emul = EMUL_4;
                    LMUL_8:  lsu_emul = EMUL_8;
                endcase
            end
            {VSEW_16, VSEW_8 },
            {VSEW_32, VSEW_16}: begin   // EEW / SEW = 2
                case (lmul_i)
                    LMUL_F8,
                    LMUL_F4,
                    LMUL_F2: lsu_emul = EMUL_1;
                    LMUL_1:  lsu_emul = EMUL_2;
                    LMUL_2:  lsu_emul = EMUL_4;
                    LMUL_4:  lsu_emul = EMUL_8;
                endcase
            end
            {VSEW_32, VSEW_8 }: begin   // EEW / SEW = 4
                case (lmul_i)
                    LMUL_F8,
                    LMUL_F4: lsu_emul = EMUL_1;
                    LMUL_F2: lsu_emul = EMUL_2;
                    LMUL_1:  lsu_emul = EMUL_4;
                    LMUL_2:  lsu_emul = EMUL_8;
                endcase
            end
        endcase
    end

    cfg_emul emul;
    always_comb begin
        emul = COMB_INIT_ZERO ? cfg_emul'('0) : cfg_emul'('x);
        case (lmul_i)
            LMUL_F8,
            LMUL_F4,
            LMUL_F2,
            LMUL_1: emul = EMUL_1;
            LMUL_2: emul = EMUL_2;
            LMUL_4: emul = EMUL_4;
            LMUL_8: emul = EMUL_8;
        endcase
        case (unit_i)
            UNIT_LSU: emul = lsu_emul;
            UNIT_ALU: begin
                if (mode_i.alu.op_mask == ALU_MASK_ARIT) begin
                    emul = EMUL_1;
                end
            end
        endcase
    end

    logic vs1_wide, vs2_wide, vd_wide;
    always_comb begin
        vs1_wide = COMB_INIT_ZERO ? '0 : 'x;
        vs2_wide = COMB_INIT_ZERO ? '0 : 'x;
        vd_wide  = COMB_INIT_ZERO ? '0 : 'x;
        unique case (widenarrow_i)
            OP_SINGLEWIDTH: begin
                vs1_wide = 1'b0;
                vs2_wide = 1'b0;
                vd_wide  = 1'b0;
            end
            OP_WIDENING: begin
                vs1_wide = 1'b0;
                vs2_wide = 1'b0;
                vd_wide  = 1'b1;
            end
            OP_WIDENING_VS2: begin
                vs1_wide = 1'b0;
                vs2_wide = 1'b1;
                vd_wide  = 1'b1;
            end
            OP_NARROWING: begin
                vs1_wide = 1'b1;
                vs2_wide = 1'b1;
                vd_wide  = 1'b0;
            end
        endcase
        // no wide vregs for fractional LMUL
        if (lmul_i[2]) begin
            vs1_wide = 1'b0;
            vs2_wide = 1'b0;
            vd_wide  = 1'b0;
        end
    end

    logic [31:0] vs1_hazards, vs2_hazards, vd_hazards;
    always_comb begin
        vs1_hazards = COMB_INIT_ZERO ? '0 : 'x;
        unique case ({emul, vs1_wide})
            {EMUL_1, 1'b0}: begin
                vs1_hazards = rs1_i.vreg ? (32'h00000001 <<  rs1_i.r.vaddr              ) : 32'b0;
            end
            {EMUL_1, 1'b1},
            {EMUL_2, 1'b0}: begin
                vs1_hazards = rs1_i.vreg ? (32'h00000003 << {rs1_i.r.vaddr[4:1], 1'b0  }) : 32'b0;
            end
            {EMUL_2, 1'b1},
            {EMUL_4, 1'b0}: begin
                vs1_hazards = rs1_i.vreg ? (32'h0000000F << {rs1_i.r.vaddr[4:2], 2'b00 }) : 32'b0;
            end
            {EMUL_4, 1'b1},
            {EMUL_8, 1'b0}: begin
                vs1_hazards = rs1_i.vreg ? (32'h000000FF << {rs1_i.r.vaddr[4:3], 3'b000}) : 32'b0;
            end
        endcase
        vs2_hazards = COMB_INIT_ZERO ? '0 : 'x;
        unique case ({emul, vs2_wide})
            {EMUL_1, 1'b0}: begin
                vs2_hazards = rs2_i.vreg ? (32'h00000001 <<  rs2_i.r.vaddr              ) : 32'b0;
            end
            {EMUL_1, 1'b1},
            {EMUL_2, 1'b0}: begin
                vs2_hazards = rs2_i.vreg ? (32'h00000003 << {rs2_i.r.vaddr[4:1], 1'b0  }) : 32'b0;
            end
            {EMUL_2, 1'b1},
            {EMUL_4, 1'b0}: begin
                vs2_hazards = rs2_i.vreg ? (32'h0000000F << {rs2_i.r.vaddr[4:2], 2'b00 }) : 32'b0;
            end
            {EMUL_4, 1'b1},
            {EMUL_8, 1'b0}: begin
                vs2_hazards = rs2_i.vreg ? (32'h000000FF << {rs2_i.r.vaddr[4:3], 3'b000}) : 32'b0;
            end
        endcase
        vd_hazards = COMB_INIT_ZERO ? '0 : 'x;
        unique case ({emul, vd_wide})
            {EMUL_1, 1'b0}: begin
                vd_hazards = rd_i.vreg ? (32'h00000001 <<  rd_i.addr              ) : 32'b0;
            end
            {EMUL_1, 1'b1},
            {EMUL_2, 1'b0}: begin
                vd_hazards = rd_i.vreg ? (32'h00000003 << {rd_i.addr[4:1], 1'b0  }) : 32'b0;
            end
            {EMUL_2, 1'b1},
            {EMUL_4, 1'b0}: begin
                vd_hazards = rd_i.vreg ? (32'h0000000F << {rd_i.addr[4:2], 2'b00 }) : 32'b0;
            end
            {EMUL_4, 1'b1},
            {EMUL_8, 1'b0}: begin
                vd_hazards = rd_i.vreg ? (32'h000000FF << {rd_i.addr[4:3], 3'b000}) : 32'b0;
            end
        endcase
    end

    logic masked;
    always_comb begin
        masked = '0;
        case (unit_i)
            UNIT_LSU:  masked = mode_i.lsu.masked;
            UNIT_ALU:  masked = mode_i.alu.masked | mode_i.alu.op_mask;
            UNIT_MUL:  masked = mode_i.mul.masked;
            UNIT_SLD:  masked = mode_i.sld.masked;
            UNIT_ELEM: masked = mode_i.elem.masked;
        endcase
    end

    always_comb begin
        rd_hazards_o = vs1_hazards | vs2_hazards | {31'b0, masked};
        wr_hazards_o = vd_hazards;
        case (unit_i)
            UNIT_LSU: begin
                if (mode_i.lsu.store) begin
                    rd_hazards_o |= vd_hazards;
                    wr_hazards_o  = '0;
                end
            end
            UNIT_ALU: begin
                if (mode_i.alu.cmp) begin
                    wr_hazards_o = rd_i.vreg ? (32'h1 << rd_i.addr) : 32'b0;
                end
            end
            UNIT_MUL: begin
                if (mode_i.mul.op == MUL_VMACC) begin
                    rd_hazards_o |= vd_hazards;
                end
            end
            UNIT_ELEM: begin
                if (mode_i.elem.op != ELEM_VRGATHER) begin
                    rd_hazards_o = vs1_hazards | (rs2_i.vreg ? (32'h1 << rs2_i.r.vaddr) : 32'b0) | {31'b0, masked};
                end
            end
        endcase
    end

endmodule
