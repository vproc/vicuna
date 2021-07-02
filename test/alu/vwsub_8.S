# Copyright TU Wien
# Licensed under the ISC license, see LICENSE.txt for details
# SPDX-License-Identifier: ISC


    .text
    .global main
main:
    la              a0, vdata_start

    li              t0, 32
    vsetvli         t0, t0, e8,m2

    li              t0, 1

    vle8.v          v0, (a0)
    vwsub.vx        v4, v0, t0
    vse16.v         v4, (a0)

    la              a0, vdata_start
    la              a1, vdata_end
    j               spill_cache


    .data
    .align 10
    .global vdata_start
    .global vdata_end
vdata_start:
    .word           0x323b3f47
    .word           0xc7434b3a
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
    .word           0x46424949
    .word           0x494a4d51
    .word           0x49413c38
    .word           0x3e514143
    .word           0x47525353
    .word           0x514e5052
    .word           0x525a5b58
    .word           0x5e575254
    .word           0x56545058
    .word           0x5a534947
    .word           0xc7434b3a
    .word           0x4e515051
    .word           0x5a4b4545
    .word           0x454c4342
    .word           0x40504a3f
    .word           0x4448535a
vdata_end:

    .align 10
    .global vref_start
    .global vref_end
vref_start:
    .word           0x003e0046
    .word           0x0031003a
    .word           0x004a0039
    .word           0xffc60042
    .word           0x002d0031
    .word           0x002f002e
    .word           0x00490050
    .word           0xffe7003f
    .word           0x0037003a
    .word           0x003e0043
    .word           0x004c0053
    .word           0x00360041
    .word           0x004f0048
    .word           0x005d004a
    .word           0x004b0049
    .word           0x004b004b
    .word           0x46424949
    .word           0x494a4d51
    .word           0x49413c38
    .word           0x3e514143
    .word           0x47525353
    .word           0x514e5052
    .word           0x525a5b58
    .word           0x5e575254
    .word           0x56545058
    .word           0x5a534947
    .word           0xc7434b3a
    .word           0x4e515051
    .word           0x5a4b4545
    .word           0x454c4342
    .word           0x40504a3f
    .word           0x4448535a
vref_end:
