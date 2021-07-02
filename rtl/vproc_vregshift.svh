// Copyright TU Wien
// Licensed under the ISC license, see LICENSE.txt for details
// SPDX-License-Identifier: ISC


`ifndef VPROC_VREGSHIFT_SVH
`define VPROC_VREGSHIFT_SVH

// shift register assignment for a vreg operand shift register with support for
// narrow operands: the lower operand halfword (i.e., the lower OP_W/2 bytes)
// are taken from the upper operand halfword if neither fetch_info.fetch nor
// fetch_info.shift are asserted
`define VREGSHIFT_OPERAND_NARROW(VREG_W, OP_W, fetch_info, vreg_i, shift_q, shift_d) \
    always_comb begin                                                                \
        shift_d = shift_q;                                                           \
        if (fetch_info.shift) begin                                                  \
            shift_d = vreg_i;                                                        \
            if (~fetch_info.fetch) begin                                             \
                shift_d[VREG_W-OP_W-1:0] = shift_q[VREG_W-1:OP_W];                   \
            end                                                                      \
        end                                                                          \
        shift_d[OP_W/2-1:0] = vreg_i[OP_W/2-1:0];                                    \
        if (~fetch_info.fetch) begin                                                 \
            if (fetch_info.shift) begin                                              \
                shift_d[OP_W/2-1:0] = shift_q[(OP_W*3)/2-1:OP_W  ];                  \
            end else begin                                                           \
                shift_d[OP_W/2-1:0] = shift_q[ OP_W     -1:OP_W/2];                  \
            end                                                                      \
        end                                                                          \
    end

// shift register assignment for a vreg operand shift register with support for
// element-wise shifting: the lower operand byte/halfword/word (i.e., the lower
// 8, 16 or 32 bytes) are taken from the next-highest byte/halfword/word if
// neither fetch_info.fetch nor fetch_info.shift are asserted; additionally, if
// hold is asserted, then the lowest SHIFT_W-8 bit retain their current value
// (hence if neither hold nor shift is asserted, then the entire shift register
// retains its current value)
`define VREGSHIFT_OPERAND_VSEW(VREG_W, SHIFT_W, fetch_info, hold, eew, vreg_i, shift_q, shift_d) \
    always_comb begin                                                                            \
        shift_d = shift_q;                                                                       \
        if (fetch_info.shift) begin                                                              \
            shift_d = vreg_i;                                                                    \
            if (~fetch_info.fetch) begin                                                         \
                shift_d[VREG_W-SHIFT_W-1:0] = shift_q[VREG_W-1:SHIFT_W];                         \
            end                                                                                  \
        end                                                                                      \
        if (~(hold)) begin                                                                       \
            shift_d[SHIFT_W-9:0] = vreg_i[SHIFT_W-9:0];                                          \
            if (~fetch_info.fetch) begin                                                         \
                if (fetch_info.shift) begin                                                      \
                    shift_d[SHIFT_W-9:0] = shift_q[2*SHIFT_W-9:SHIFT_W];                         \
                end else begin                                                                   \
                    shift_d[SHIFT_W-9:0] = COMB_INIT_ZERO ? '0 : 'x;                             \
                    case(eew)                                                                    \
                        VSEW_8:  shift_d[SHIFT_W-9:0] = shift_q[SHIFT_W-1 :8 ];                  \
                        VSEW_16: shift_d[SHIFT_W-9:0] = shift_q[SHIFT_W+7 :16];                  \
                        VSEW_32: shift_d[SHIFT_W-9:0] = shift_q[SHIFT_W+23:32];                  \
                    endcase                                                                      \
                end                                                                              \
            end                                                                                  \
        end                                                                                      \
    end

// shift register assignment for an operand mask shift register; note that for
// an EEW of 8, fetch_info.shift is asserted every cycle
`define VREGSHIFT_OPMASK(VREG_W, OP_W, fetch_info, eew, vmsk_i, shift_q, shift_d)       \
    always_comb begin                                                                   \
        shift_d = shift_q;                                                              \
        if (fetch_info.shift) begin                                                     \
            shift_d = vmsk_i;                                                           \
            if (~fetch_info.fetch) begin                                                \
                shift_d[VREG_W-OP_W/8-1:0] = shift_q[VREG_W-1:OP_W/8];                  \
            end                                                                         \
        end                                                                             \
        shift_d[(OP_W*3)/32-1:0] = vmsk_i[(OP_W*3)/32-1:0];                             \
        if (~fetch_info.fetch) begin                                                    \
            if (fetch_info.shift) begin                                                 \
                shift_d[(OP_W*3)/32-1:0] = shift_q[(OP_W*7)/32-1:OP_W/8];               \
            end else begin                                                              \
                shift_d[(OP_W*3)/32-1:0] = COMB_INIT_ZERO ? '0 : 'x;                    \
                case (eew)                                                              \
                    VSEW_16: shift_d[(OP_W*3)/32-1:0] = shift_q[(OP_W*5)/32-1:OP_W/16]; \
                    VSEW_32: shift_d[(OP_W*3)/32-1:0] = shift_q[(OP_W*4)/32-1:OP_W/32]; \
                endcase                                                                 \
            end                                                                         \
        end                                                                             \
    end

// shift register assignment for a vreg result shift register with support for
// narrow results: the upper result halfword (i.e., the upper OP_W/2 bytes) are
// taken from the lower result halfword if store_info.shift is not asserted
`define VREGSHIFT_RESULT_NARROW(VREG_W, OP_W, store_info, res_i, shift_q, shift_d) \
    always_comb begin                                                              \
        shift_d = shift_q;                                                         \
        if (store_info.shift) begin                                                \
            shift_d = {res_i, shift_q[VREG_W-1:OP_W]};                             \
        end else begin                                                             \
            shift_d[VREG_W-1:VREG_W-OP_W/2] = res_i[OP_W/2-1:0];                   \
        end                                                                        \
    end

// shift register assignment for a result mask shift register with support for
// narrow results: the upper mask halfword (i.e., the upper OP_W/16 bytes) are
// taken from the lower mask halfword if store_info.shift is not asserted
`define VREGSHIFT_RESMASK_NARROW(VREG_W, OP_W, store_info, resmsk_i, shift_q, shift_d) \
    always_comb begin                                                                  \
        shift_d = shift_q;                                                             \
        if (store_info.shift) begin                                                    \
            shift_d = {resmsk_i, shift_q[VREG_W/8-1:OP_W/8]};                          \
        end else begin                                                                 \
            shift_d[VREG_W/8-1:VREG_W/8-OP_W/16] = resmsk_i[OP_W/16-1:0];              \
        end                                                                            \
    end

`endif // VPROC_VREGSHIFT_SVH
