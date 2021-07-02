# Copyright TU Wien
# Licensed under the ISC license, see LICENSE.txt for details
# SPDX-License-Identifier: ISC


    .text
    .global main
main:
    la              a0, vdata_start

    li              t0, 16
    vsetvli         t0, t0, e32,m4

    vle32.v         v0, (a0)
    addi            a1, a0, 64
    vle32.v         v4, (a1)
    vrgather.vv     v8, v0, v4
    vse32.v         v8, (a0)

    la              a0, vdata_start
    la              a1, vdata_end
    j               spill_cache


    .data
    .align 10
    .global vdata_start
    .global vdata_end
vdata_start:
    .word           0x323b3f47
    .word           0x47434b3a
    .word           0x302f2e32
    .word           0xe8404a51
    .word           0x3f44383b
    .word           0x37424d54
    .word           0x5e4b5049
    .word           0x4c4c4c4a
    .word           0x4a505f3e
    .word           0x485e5455
    .word           0x4d4c4a41
    .word           0x373b5451
    .word           0x41454c45
    .word           0x3a3e3738
    .word           0x312f2e2f
    .word           0x3d433f45
    .word           0x0000000f
    .word           0x0000000e
    .word           0x0000000d
    .word           0x0000000c
    .word           0x000000fb
    .word           0x0000000a
    .word           0x00000009
    .word           0x00000008
    .word           0x00040007
    .word           0x00000006
    .word           0x00000005
    .word           0x00000004
    .word           0x80000003
    .word           0x00000002
    .word           0x00000001
    .word           0x00000000
vdata_end:

    .align 10
    .global vref_start
    .global vref_end
vref_start:
    .word           0x3d433f45
    .word           0x312f2e2f
    .word           0x3a3e3738
    .word           0x41454c45
    .word           0x00000000
    .word           0x4d4c4a41
    .word           0x485e5455
    .word           0x4a505f3e
    .word           0x00000000
    .word           0x5e4b5049
    .word           0x37424d54
    .word           0x3f44383b
    .word           0x00000000
    .word           0x302f2e32
    .word           0x47434b3a
    .word           0x323b3f47
    .word           0x0000000f
    .word           0x0000000e
    .word           0x0000000d
    .word           0x0000000c
    .word           0x000000fb
    .word           0x0000000a
    .word           0x00000009
    .word           0x00000008
    .word           0x00040007
    .word           0x00000006
    .word           0x00000005
    .word           0x00000004
    .word           0x80000003
    .word           0x00000002
    .word           0x00000001
    .word           0x00000000
vref_end:
