# Copyright TU Wien
# Licensed under the Solderpad Hardware License v2.1, see LICENSE.txt for details
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1


    .text
    .balign 4
    .global main
main:
    li              t0, 65536
    li              a0, 256
    li              a1, 256
    li              a2, 256
    la              a3, vdata_start
    li              a4, 256
    la              a5, vdata_start
    add             a5, a5, t0
    li              a6, 256
    la              a7, vdata_start
    add             a7, a7, t0
    add             a7, a7, t0
    li              t0, 256

# void gemm(size_t n, size_t m, size_t k,
#           const int8_t* a,   // m * k matrix
#           size_t lda,
#           const int8_t* b,   // k * n matrix
#           size_t ldb,
#           int8_t* c,         // m * n matrix
#           size_t ldc)
#
#  c += a*b (alpha=1, no transpose on input matrices)
#  matrices stored in C row-major order

#define n a0
#define m a1
#define k a2
#define ap a3
#define astride a4
#define bp a5
#define bstride a6
#define cp a7
#define cstride t0
#define kt t1
#define nt t2
#define bnp t3
#define cnp t4
#define akp t5
#define bkp s0
#define nvl s1
#define ccp s2
#define amp s3

# This version holds a 8*VLMAX block of C matrix in vector registers
# in inner loop, but otherwise does not cache or TLB tiling.

gemm_nn:
    # Check for zero size matrices
    beqz            n, exit
    beqz            m, exit
    beqz            k, exit

    slti            t6, m, 8
    bnez            t6, end_rows

    vsetvli         nvl, n, e8,m4,tu,mu

c_row_loop: # Loop across rows of C blocks

    mv              nt, n   # Initialize n counter for next row of C blocks

    mv              bnp, bp # Initialize B n-loop pointer to start
    mv              cnp, cp # Initialize C n-loop pointer

c_col_loop: # Loop across one row of C blocks

    mv              akp, ap   # reset pointer into A to beginning

    vle8.v          v16, (bnp)
    mv              bkp, bnp  # step to next column in B matrix

    vle8.v          v0, (cnp)
    add             ccp, cnp, cstride
    vle8.v          v4, (ccp)
    add             ccp, ccp, cstride
    vle8.v          v8, (ccp)
    lb              t6, (akp)
    vmacc.vx        v0, t6, v16
    add             ccp, ccp, cstride
    vle8.v          v12, (ccp)
    add             amp, akp, astride
    lb              t6, (amp)
    vmacc.vx        v4, t6, v16

    add             bkp, bkp, bstride
    vle8.v          v24, (bkp)
    add             amp, amp, astride
    lb              t6, (amp)
    vmacc.vx        v8, t6, v16

    add             amp, amp, astride
    lb              t6, (amp)
    vmacc.vx        v12, t6, v16

    addi            kt, k, -2
    beqz            kt, k_loop_end

k_loop:
    addi            akp, akp, 4
    lb              t6, (akp)
    vmacc.vx        v0, t6, v24
    add             bkp, bkp, bstride
    add             amp, akp, astride
    lb              t6, (amp)
    vmacc.vx        v4, t6, v24
    vle8.v          v16, (bkp)
    add             amp, amp, astride
    lb              t6, (amp)
    vmacc.vx        v8, t6, v24
    add             amp, amp, astride
    lb              t6, (amp)
    vmacc.vx        v12, t6, v24

    addi            kt, kt, -2    # Decrement k counter

    addi            akp, akp, 4
    lb              t6, (akp)
    vmacc.vx        v0, t6, v16
    add             bkp, bkp, bstride
    add             amp, akp, astride
    lb              t6, (amp)
    vmacc.vx        v4, t6, v16
    vle8.v          v24, (bkp)
    add             amp, amp, astride
    lb              t6, (amp)
    vmacc.vx        v8, t6, v16
    add             amp, amp, astride
    lb              t6, (amp)
    vmacc.vx        v12, t6, v16


    bnez            kt, k_loop

k_loop_end:
    addi            akp, akp, 4
    lb              t6, (akp)
    vmacc.vx        v0, t6, v24
    add             amp, akp, astride
    lb              t6, (amp)
    vmacc.vx        v4, t6, v24
    add             amp, amp, astride
    lb              t6, (amp)
    vmacc.vx        v8, t6, v24
    add             amp, amp, astride
    lb              t6, (amp)
    vse8.v          v0, (cnp)
    vmacc.vx        v12, t6, v24
    add             cnp, cnp, nvl       # Move C block pointer over
    add             ccp, cnp, cstride
    vse8.v          v4, (ccp)
    add             bnp, bnp, nvl       # Move B block pointer over
    add             ccp, ccp, cstride
    vse8.v          v8, (ccp)
    sub             nt, nt, nvl         # Decrement element count in n dimension
    add             ccp, ccp, cstride
    vse8.v          v12, (ccp)

    bnez nt, c_col_loop                 # Any more to do?

    # Move to next set of rows
    addi            m, m, -4        # Did 4 rows above
    slli            t6, astride, 2  # Multiply astride by 4
    add             ap, ap, t6      # Move A matrix pointer down 4 rows
    slli            t6, cstride, 2  # Multiply cstride by 4
    add             cp, cp, t6      # Move C matrix pointer down 4 rows

    slti            t6, m, 8
    beqz            t6, c_row_loop

    # Handle end of matrix with fewer than 8 rows.
    # Can use smaller versions of above decreasing in powers-of-2 depending on code-size concerns.
end_rows:
    # Not done.

exit:
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
