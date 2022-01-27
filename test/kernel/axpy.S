# Copyright TU Wien
# Licensed under the Solderpad Hardware License v2.1, see LICENSE.txt for details
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1


    .text
    .balign 4
    .global main
main:
    li              a0, 65536
    la              a1, vdata_start
    add             a2, a1, a0
    li              a3, 7

# void axpy(size_t n, const int8_t a, const int8_t *x, int8_t *y)
# {
#   size_t i;
#   for (i = 0; i < n; i++)
#     y[i] = a * x[i] + y[i];
# }

# register arguments:
#     a0      n
#     a1      x
#     a2      y
#     a3      a

    vsetvli         t0, a0, e8,m4

    mv              t2, a2

    vle8.v          v0, (a1)
    add             a1, a1, t0
    vle8.v          v16, (a2)
    add             a2, a2, t0

    vle8.v          v4, (a1)
    add             a1, a1, t0
    vle8.v          v20, (a2)
    add             a2, a2, t0

    sub             a0, a0, t0
    beqz            a0, abort0

axpy:
    vmacc.vx        v16, a3, v0
    vle8.v          v8, (a1)
    add             a1, a1, t0
    vle8.v          v24, (a2)
    add             a2, a2, t0
    vse8.v          v16, (t2)
    add             t2, t2, t0

    sub             a0, a0, t0
    beqz            a0, abort1

    vmacc.vx        v20, a3, v4
    vle8.v          v12, (a1)
    add             a1, a1, t0
    vle8.v          v28, (a2)
    add             a2, a2, t0
    vse8.v          v20, (t2)
    add             t2, t2, t0

    sub             a0, a0, t0
    beqz            a0, abort2

    vmacc.vx        v24, a3, v8
    vle8.v          v0, (a1)
    add             a1, a1, t0
    vle8.v          v16, (a2)
    add             a2, a2, t0
    vse8.v          v24, (t2)
    add             t2, t2, t0

    sub             a0, a0, t0
    beqz            a0, abort3

    vmacc.vx        v28, a3, v12
    vle8.v          v4, (a1)
    add             a1, a1, t0
    vle8.v          v20, (a2)
    add             a2, a2, t0
    vse8.v          v28, (t2)
    add             t2, t2, t0

    sub             a0, a0, t0
    bnez            a0, axpy

abort0:
    vmacc.vx        v16, a3, v0
    vse8.v          v16, (t2)
    j               end

abort1:
    vmacc.vx        v20, a3, v4
    vse8.v          v20, (t2)
    j               end

abort2:
    vmacc.vx        v24, a3, v8
    vse8.v          v24, (t2)
    j               end

abort3:
    vmacc.vx        v28, a3, v12
    vse8.v          v28, (t2)

end:
    jr              x0

    .data
    .align 10
    .global vdata_start
    .global vdata_end
vdata_start:
    .word           0x00000000
vdata_end:

    .align 10
    .global vref_start
    .global vref_end
vref_start:
    .word           0x00000000
vref_end:
