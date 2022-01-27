# Copyright TU Wien
# Licensed under the Solderpad Hardware License v2.1, see LICENSE.txt for details
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1


    .text
    .balign 4
    .global main
main:
    li              t2, 65536
    vsetvli         t2, t2, e8
    mv              a3, t2          # width is VLMAX
    li              a4, 65536       # total size is 65536 pixel
    la              a0, vdata_start
    add             a1, a0, a4
    add             a2, a1, a4
    addi            t2, t2, -1

conv3x3:
    # a0: out_addr
    # a1: in_addr
    # a2: wgts_addr
    # a3: row_stride
    # a4: image size (row_stride * height)

    add             a4, a4, a1

.L0:
    sub             t3, a1, a3
    vle16.v         v8, (t3)
    li              t4, 2
    add             t3, t3, a3
    add             t3, t3, a3
    vle16.v         v10, (t3)
    vmul.vx         v0, v8, t4
    vmul.vx         v1, v9, t4
    add             t3, t3, a3
    add             t3, t3, a3
    vle16.v         v12, (t3)
    vmul.vx         v2, v10, t4
    vmul.vx         v3, v11, t4
    li              t5, 4
    vmacc.vx        v0, t5, v9
    vmacc.vx        v1, t5, v10
    add             t3, t3, a3
    add             t3, t3, a3
    vle16.v         v14, (t3)
    vmul.vx         v4, v12, t4
    vmul.vx         v5, v13, t4
    vmacc.vx        v2, t5, v11
    vmacc.vx        v3, t5, v12
    vmul.vx         v6, v14, t4
    vmul.vx         v7, v15, t4
    add             t3, t3, a3
    add             t3, t3, a3
    vle8.v          v16, (t3)
    vmacc.vx        v4, t5, v13
    vmacc.vx        v5, t5, v14
    vmacc.vx        v6, t5, v15
    vmacc.vx        v7, t5, v16
    li              t4, 2
    vmacc.vx        v0, t4, v10
    vmacc.vx        v1, t4, v11
    add             t3, t3, a3
    vmacc.vx        v2, t4, v12
    vle8.v          v17, (t3)
    vmacc.vx        v3, t4, v13
    vmacc.vx        v4, t4, v14
    vslide1up.vx    v18, v8, x0
    vmacc.vx        v5, t4, v15
    vslide1up.vx    v19, v9, x0
    vmacc.vx        v6, t4, v16
    vslide1up.vx    v20, v10, x0
    vmacc.vx        v7, t4, v17
    li              t4, 1
    vmacc.vx        v0, t4, v18
    vslide1up.vx    v21, v11, x0
    vmacc.vx        v1, t4, v19
    vslide1up.vx    v22, v12, x0
    vmacc.vx        v2, t4, v20
    vslide1up.vx    v23, v13, x0
    vmacc.vx        v3, t4, v21
    vslide1up.vx    v24, v14, x0
    vmacc.vx        v4, t4, v22
    vslide1up.vx    v25, v15, x0
    vmacc.vx        v5, t4, v23
    vmacc.vx        v6, t4, v24
    vmacc.vx        v7, t4, v25
    li              t4, 2
    vmacc.vx        v0, t4, v19
    vmacc.vx        v1, t4, v20
    vmacc.vx        v2, t4, v21
    vmacc.vx        v3, t4, v22
    vmacc.vx        v4, t4, v23
    vslide1up.vx    v26, v16, x0
    vmacc.vx        v5, t4, v24
    vmacc.vx        v6, t4, v25
    vmacc.vx        v7, t4, v26
    li              t4, 1
    vmacc.vx        v0, t4, v20
    vmacc.vx        v1, t4, v21
    vmacc.vx        v2, t4, v22
    vmacc.vx        v3, t4, v23
    vmacc.vx        v4, t4, v24
    vslide1up.vx    v27, v17, x0
    vmacc.vx        v5, t4, v25
    vslide1down.vx  v18, v8, x0
    vmacc.vx        v6, t4, v26
    vslide1down.vx  v19, v9, x0
    vmacc.vx        v7, t4, v27
    li              t4, 1
    vslide1down.vx  v20, v10, x0
    vmacc.vx        v0, t4, v18
    vslide1down.vx  v21, v11, x0
    vmacc.vx        v1, t4, v19
    vslide1down.vx  v22, v12, x0
    vmacc.vx        v2, t4, v20
    vslide1down.vx  v23, v13, x0
    vmacc.vx        v3, t4, v21
    vslide1down.vx  v24, v14, x0
    vmacc.vx        v4, t4, v22
    vslide1down.vx  v25, v15, x0
    vmacc.vx        v5, t4, v23
    vmacc.vx        v6, t4, v24
    vmacc.vx        v7, t4, v25
    li              t4, 2
    vmacc.vx        v0, t4, v19
    vmacc.vx        v1, t4, v20
    vmacc.vx        v2, t4, v21
    vmacc.vx        v3, t4, v22
    vmacc.vx        v4, t4, v23
    vslide1down.vx  v26, v16, x0
    vmacc.vx        v5, t4, v24
    vmacc.vx        v6, t4, v25
    vmacc.vx        v7, t4, v26
    li              t4, 1
    vmacc.vx        v0, t4, v20
    vmacc.vx        v1, t4, v21
    vmacc.vx        v2, t4, v22
    vse8.v          v0, (a0)
    vmacc.vx        v3, t4, v23
    add             t3, a0, a3
    vse8.v          v1, (t3)
    vmacc.vx        v4, t4, v24
    vslide1down.vx  v27, v17, x0
    add             t3, t3, a3
    vse8.v          v2, (t3)
    vmacc.vx        v5, t4, v25
    add             t3, t3, a3
    vse8.v          v3, (t3)
    vmacc.vx        v6, t4, v26
    add             t3, t3, a3
    vse8.v          v4, (t3)
    vmacc.vx        v7, t4, v27
    add             t3, t3, a3
    vse8.v          v5, (t3)
    add             t3, t3, a3
    vse8.v          v6, (t3)
    add             t3, t3, a3
    vse8.v          v7, (t3)

    slli            t3, a3, 3
    add             a1, a1, t3
    add             a0, a0, t3
    blt             a1, a4, .L0

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
