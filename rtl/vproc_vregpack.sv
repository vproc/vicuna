// Copyright TU Wien
// Licensed under the ISC license, see LICENSE.txt for details
// SPDX-License-Identifier: ISC


// packing results into vector registers
module vproc_vregpack #(
        parameter int unsigned     OP_W,   // operand size
        parameter bit              COMB_INIT_ZERO = 1'b0
    )(
        input  vproc_pkg::cfg_vsew vsew_i,
        input  logic [OP_W  -1:0]  result_i,
        input  logic               result_narrow_i,
        input  logic [OP_W/8-1:0]  result_mask_i,
        output logic [OP_W  -1:0]  vd_o,
        output logic [OP_W/8-1:0]  vdmsk_o
    );

    import vproc_pkg::*;

    always_comb begin

        // the register write value is taken from the result
        vd_o    = COMB_INIT_ZERO ? '0 : 'x;
        vdmsk_o = COMB_INIT_ZERO ? '0 : 'x;
        if (result_narrow_i) begin
            // retain least significant bits for narrowing ops
            unique case (vsew_i)
                VSEW_16: begin
                    for (int i = 0; i < OP_W / 16; i++) begin
                        vd_o   [i*8  +: 8 ] = result_i     [i*16 +: 8 ];
                        vdmsk_o[i         ] = result_mask_i[i*2       ];
                    end
                end
                VSEW_32: begin
                    for (int i = 0; i < OP_W / 32; i++) begin
                        vd_o   [i*16 +: 16] = result_i     [i*32 +: 16];
                        vdmsk_o[i*2       ] = result_mask_i[i*4       ];
                        vdmsk_o[i*2  +  1 ] = result_mask_i[i*4       ];
                    end
                end
                default: ;
            endcase
        end else begin
            vd_o    = result_i;
            vdmsk_o = result_mask_i;
        end

    end

endmodule
