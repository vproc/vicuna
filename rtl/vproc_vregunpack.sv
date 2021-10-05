// Copyright TU Wien
// Licensed under the ISC license, see LICENSE.txt for details
// SPDX-License-Identifier: ISC


// unpacking vector registers to operands
module vproc_vregunpack #(
        parameter int unsigned     OP_W           = 64,  // operand size
        parameter bit              DONT_CARE_ZERO = 1'b0 // initialize don't care values to zero
    )(
        input  vproc_pkg::cfg_vsew vsew_i,
        input  vproc_pkg::op_regs  rs1_i,
        input  logic [OP_W  -1:0]  vs1_i,
        input  logic               vs1_narrow_i,
        input  logic               vs1_sigext_i,
        input  logic [OP_W  -1:0]  vs2_i,
        input  logic               vs2_narrow_i,
        input  logic               vs2_sigext_i,
        input  logic [OP_W/8-1:0]  vmsk_i,
        output logic [OP_W  -1:0]  operand1_o,
        output logic [OP_W  -1:0]  operand2_o,
        output logic [OP_W/8-1:0]  operand_mask_o
    );

    import vproc_pkg::*;

    always_comb begin

        // operand 1 is either filled with the value of xreg rs1 or vreg vs1
        operand1_o = DONT_CARE_ZERO ? '0 : 'x;
        if (~rs1_i.vreg) begin
            unique case (vsew_i)
                VSEW_8: begin
                    for (int i = 0; i < OP_W / 8; i++) begin
                        operand1_o[8*i  +: 8 ] = rs1_i.r.xval[7 :0];
                    end
                end
                VSEW_16: begin
                    for (int i = 0; i < OP_W / 16; i++) begin
                        operand1_o[16*i +: 16] = rs1_i.r.xval[15:0];
                    end
                end
                VSEW_32: begin
                    for (int i = 0; i < OP_W / 32; i++) begin
                        operand1_o[32*i +: 32] = rs1_i.r.xval;
                    end
                end
                default: ;
            endcase
        end else begin
            if (vs1_narrow_i) begin
                // zero-extend or sign-extend values for widening ops
                unique case (vsew_i)
                    VSEW_16: begin
                        for (int i = 0; i < OP_W / 16; i++) begin
                            operand1_o[16*i +: 16] = {{8 {vs1_sigext_i & vs1_i[8 *i + 7 ]}}, vs1_i[8 *i +: 8 ]};
                        end
                    end
                    VSEW_32: begin
                        for (int i = 0; i < OP_W / 32; i++) begin
                            operand1_o[32*i +: 32] = {{16{vs1_sigext_i & vs1_i[16*i + 15]}}, vs1_i[16*i +: 16]};
                        end
                    end
                    default: ;
                endcase
            end else begin
                operand1_o = vs1_i;
            end
        end

        // operand 2 is filled with vreg vs2
        operand2_o = DONT_CARE_ZERO ? '0 : 'x;
        if (vs2_narrow_i) begin
            // zero-extend or sign-extend values for widening ops
            unique case (vsew_i)
                VSEW_16: begin
                    for (int i = 0; i < OP_W / 16; i++) begin
                        operand2_o[16*i +: 16] = {{8 {vs2_sigext_i & vs2_i[8 *i + 7 ]}}, vs2_i[8 *i +: 8 ]};
                    end
                end
                VSEW_32: begin
                    for (int i = 0; i < OP_W / 32; i++) begin
                        operand2_o[32*i +: 32] = {{16{vs2_sigext_i & vs2_i[16*i + 15]}}, vs2_i[16*i +: 16]};
                    end
                end
                default: ;
            endcase
        end else begin
            operand2_o = vs2_i;
        end

        // convert element mask to byte mask
        operand_mask_o = DONT_CARE_ZERO ? '0 : 'x;
        unique case (vsew_i)
            VSEW_8: begin
                operand_mask_o = vmsk_i;
            end
            VSEW_16: begin
                for (int i = 0; i < OP_W / 16; i++) begin
                    operand_mask_o[i*2]   = vmsk_i[i];
                    operand_mask_o[i*2+1] = vmsk_i[i];
                end
            end
            VSEW_32: begin
                for (int i = 0; i < OP_W / 32; i++) begin
                    operand_mask_o[i*4]   = vmsk_i[i];
                    operand_mask_o[i*4+1] = vmsk_i[i];
                    operand_mask_o[i*4+2] = vmsk_i[i];
                    operand_mask_o[i*4+3] = vmsk_i[i];
                end
            end
            default: ;
        endcase

    end

endmodule
