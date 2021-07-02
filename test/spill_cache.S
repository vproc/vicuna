# Copyright TU Wien
# Licensed under the ISC license, see LICENSE.txt for details
# SPDX-License-Identifier: ISC


    .text
    .balign 4
    .global spill_cache
spill_cache:
    li              t0, 0x10000

    add             a0, a0, t0
    add             a1, a1, t0
    mv              t1, a0
.spill_cache_0:
    lw              x0,   (t1)
    lw              x0,  4(t1)
    lw              x0,  8(t1)
    lw              x0, 12(t1)
    addi            t1, t1, 16
    ble             t1, a1, .spill_cache_0

    add             a0, a0, t0
    add             a1, a1, t0
.spill_cache_1:
    lw              x0,   (a0)
    lw              x0,  4(a0)
    lw              x0,  8(a0)
    lw              x0, 12(a0)
    addi            a0, a0, 16
    ble             a0, a1, .spill_cache_1

    jr              x0
