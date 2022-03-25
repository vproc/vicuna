# Copyright TU Wien
# Licensed under the Solderpad Hardware License v2.1, see LICENSE.txt for details
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1


    .text
    .global main
main:
    la              a0, vdata_start

    li              t0, 128
    vsetvli         t0, t0, e8,m8,tu,mu

    vmv.v.x         v8, x0

    vle8.v          v0, (a0)
    vslideup.vi     v8, v0, 1
    vse8.v          v8, (a0)

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
    .word           0x38404a51
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
    .word           0x4744544f
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
    .word           0x3b3f4700
    .word           0x434b3a32
    .word           0x2f2e3247
    .word           0x404a5130
    .word           0x44383b38
    .word           0x424d543f
    .word           0x4b504937
    .word           0x4c4c4a5e
    .word           0x505f3e4c
    .word           0x5e54554a
    .word           0x4c4a4148
    .word           0x3b54514d
    .word           0x454c4537
    .word           0x3e373841
    .word           0x2f2e2f3a
    .word           0x433f4531
    .word           0x4249493d
    .word           0x4a4d5146
    .word           0x413c3849
    .word           0x51414349
    .word           0x5253533e
    .word           0x4e505247
    .word           0x5a5b5851
    .word           0x57525452
    .word           0x5450585e
    .word           0x53494756
    .word           0x44544f5a
    .word           0x51505147
    .word           0x4b45454e
    .word           0x4c43425a
    .word           0x504a3f45
    .word           0x48535a40
vref_end:
