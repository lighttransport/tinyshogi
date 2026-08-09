/* A64FX SVE INT8 SDOT 4x5 GEMM tile.
 * Four A vectors and five broadcast B vectors feed twenty independent
 * accumulators.  The inner body is deliberately under the A64FX 48-uop
 * short-loop threshold and keeps the SDOT pipes busy while B is reused.
 */
    .arch armv8.2-a+sve
    .text
    .align 6
    .global tinyshogi_a64fx_sdot_gemm_4x5
    .type tinyshogi_a64fx_sdot_gemm_4x5, %function

tinyshogi_a64fx_sdot_gemm_4x5:
    stp     x19, x20, [sp, #-96]!
    stp     x21, x22, [sp, #16]
    stp     d8, d9, [sp, #32]
    stp     d10, d11, [sp, #48]
    stp     d12, d13, [sp, #64]
    stp     d14, d15, [sp, #80]
    ptrue   p0.b

    /* x0=K, x1=A, x2=B, x3=C, x4=ldc */
    lsr     x19, x0, #2              /* number of packed SDOT steps */
    cbz     x19, .Lsdot45_done
    lsl     x20, x4, #2              /* C column stride in bytes */

    eor     z2.d, z2.d, z2.d
    eor     z3.d, z3.d, z3.d
    eor     z4.d, z4.d, z4.d
    eor     z5.d, z5.d, z5.d
    eor     z6.d, z6.d, z6.d
    eor     z7.d, z7.d, z7.d
    eor     z8.d, z8.d, z8.d
    eor     z9.d, z9.d, z9.d
    eor     z10.d, z10.d, z10.d
    eor     z11.d, z11.d, z11.d
    eor     z12.d, z12.d, z12.d
    eor     z13.d, z13.d, z13.d
    eor     z14.d, z14.d, z14.d
    eor     z15.d, z15.d, z15.d
    eor     z16.d, z16.d, z16.d
    eor     z17.d, z17.d, z17.d
    eor     z18.d, z18.d, z18.d
    eor     z19.d, z19.d, z19.d
    eor     z20.d, z20.d, z20.d
    eor     z21.d, z21.d, z21.d

    .align 6
    /* Stage two K/4 steps. A is reused while B is double-buffered, matching
     * the Fujitsu 4x5 schedule: loads are hidden under independent SDOTs. */
    cmp     x19, #2
    b.lt    .Lsdot45_tail
    ld1rw   {z22.s}, p0/z, [x2]
    ld1rw   {z23.s}, p0/z, [x2, #4]
    ld1rw   {z24.s}, p0/z, [x2, #8]
    ld1rw   {z25.s}, p0/z, [x2, #12]
    ld1rw   {z26.s}, p0/z, [x2, #16]
    ld1rw   {z27.s}, p0/z, [x2, #20]
    ld1rw   {z28.s}, p0/z, [x2, #24]
    ld1b    {z0.b}, p0/z, [x1]

.Lsdot45_loop:
    ld1b    {z1.b}, p0/z, [x1, #1, mul vl]
    sdot    z2.s, z0.b, z22.b
    sdot    z3.s, z0.b, z23.b
    ld1rw   {z29.s}, p0/z, [x2, #28]
    ld1rw   {z30.s}, p0/z, [x2, #32]
    sdot    z4.s, z0.b, z24.b
    sdot    z5.s, z0.b, z25.b
    sdot    z6.s, z0.b, z26.b
    sdot    z7.s, z1.b, z22.b
    ld1b    {z0.b}, p0/z, [x1, #2, mul vl]
    ld1rw   {z31.s}, p0/z, [x2, #36]
    sdot    z8.s, z1.b, z23.b
    sdot    z9.s, z1.b, z24.b
    sdot    z10.s, z1.b, z25.b
    sdot    z11.s, z1.b, z26.b
    ld1b    {z1.b}, p0/z, [x1, #3, mul vl]
    sdot    z12.s, z0.b, z22.b
    sdot    z13.s, z0.b, z23.b
    sdot    z14.s, z0.b, z24.b
    sdot    z15.s, z0.b, z25.b
    sdot    z16.s, z0.b, z26.b
    sdot    z17.s, z1.b, z22.b
    ld1b    {z0.b}, p0/z, [x1, #4, mul vl]
    sdot    z18.s, z1.b, z23.b
    sdot    z19.s, z1.b, z24.b
    ld1rw   {z22.s}, p0/z, [x2, #40]
    ld1rw   {z23.s}, p0/z, [x2, #44]
    sdot    z20.s, z1.b, z25.b
    sdot    z21.s, z1.b, z26.b

    ld1b    {z1.b}, p0/z, [x1, #5, mul vl]
    sdot    z2.s, z0.b, z27.b
    sdot    z3.s, z0.b, z28.b
    ld1rw   {z24.s}, p0/z, [x2, #48]
    ld1rw   {z25.s}, p0/z, [x2, #52]
    sdot    z4.s, z0.b, z29.b
    sdot    z5.s, z0.b, z30.b
    sdot    z6.s, z0.b, z31.b
    sdot    z7.s, z1.b, z27.b
    ld1b    {z0.b}, p0/z, [x1, #6, mul vl]
    ld1rw   {z26.s}, p0/z, [x2, #56]
    sdot    z8.s, z1.b, z28.b
    sdot    z9.s, z1.b, z29.b
    sdot    z10.s, z1.b, z30.b
    sdot    z11.s, z1.b, z31.b
    ld1b    {z1.b}, p0/z, [x1, #7, mul vl]
    add     x1, x1, #512
    sdot    z12.s, z0.b, z27.b
    sdot    z13.s, z0.b, z28.b
    sdot    z14.s, z0.b, z29.b
    sdot    z15.s, z0.b, z30.b
    sdot    z16.s, z0.b, z31.b
    sdot    z17.s, z1.b, z27.b
    ld1b    {z0.b}, p0/z, [x1]
    cmp     x19, #4
    sdot    z18.s, z1.b, z28.b
    sdot    z19.s, z1.b, z29.b
    ld1rw   {z27.s}, p0/z, [x2, #60]
    ld1rw   {z28.s}, p0/z, [x2, #64]
    sdot    z20.s, z1.b, z30.b
    sdot    z21.s, z1.b, z31.b
    add     x2, x2, #40
    sub     x19, x19, #2
    b.ge    .Lsdot45_loop

.Lsdot45_tail:
    cmp     x19, #1
    b.lt    .Lsdot45_store
    ld1b    {z1.b}, p0/z, [x1, #1, mul vl]
    sdot    z2.s, z0.b, z22.b
    sdot    z3.s, z0.b, z23.b
    sdot    z4.s, z0.b, z24.b
    sdot    z5.s, z0.b, z25.b
    sdot    z6.s, z0.b, z26.b
    sdot    z7.s, z1.b, z22.b
    ld1b    {z0.b}, p0/z, [x1, #2, mul vl]
    sdot    z8.s, z1.b, z23.b
    sdot    z9.s, z1.b, z24.b
    sdot    z10.s, z1.b, z25.b
    sdot    z11.s, z1.b, z26.b
    ld1b    {z1.b}, p0/z, [x1, #3, mul vl]
    sdot    z12.s, z0.b, z22.b
    sdot    z13.s, z0.b, z23.b
    sdot    z14.s, z0.b, z24.b
    sdot    z15.s, z0.b, z25.b
    sdot    z16.s, z0.b, z26.b
    sdot    z17.s, z1.b, z22.b
    sdot    z18.s, z1.b, z23.b
    sdot    z19.s, z1.b, z24.b
    sdot    z20.s, z1.b, z25.b
    sdot    z21.s, z1.b, z26.b

.Lsdot45_store:
    /* Store C column-major: each column is four 16-lane vectors. */
    mov     x21, x3
    st1w    {z2.s}, p0, [x21]
    st1w    {z7.s}, p0, [x21, #1, mul vl]
    st1w    {z12.s}, p0, [x21, #2, mul vl]
    st1w    {z17.s}, p0, [x21, #3, mul vl]
    add     x21, x21, x20
    st1w    {z3.s}, p0, [x21]
    st1w    {z8.s}, p0, [x21, #1, mul vl]
    st1w    {z13.s}, p0, [x21, #2, mul vl]
    st1w    {z18.s}, p0, [x21, #3, mul vl]
    add     x21, x21, x20
    st1w    {z4.s}, p0, [x21]
    st1w    {z9.s}, p0, [x21, #1, mul vl]
    st1w    {z14.s}, p0, [x21, #2, mul vl]
    st1w    {z19.s}, p0, [x21, #3, mul vl]
    add     x21, x21, x20
    st1w    {z5.s}, p0, [x21]
    st1w    {z10.s}, p0, [x21, #1, mul vl]
    st1w    {z15.s}, p0, [x21, #2, mul vl]
    st1w    {z20.s}, p0, [x21, #3, mul vl]
    add     x21, x21, x20
    st1w    {z6.s}, p0, [x21]
    st1w    {z11.s}, p0, [x21, #1, mul vl]
    st1w    {z16.s}, p0, [x21, #2, mul vl]
    st1w    {z21.s}, p0, [x21, #3, mul vl]

.Lsdot45_done:
    ldp     d14, d15, [sp, #80]
    ldp     d12, d13, [sp, #64]
    ldp     d10, d11, [sp, #48]
    ldp     d8, d9, [sp, #32]
    ldp     x21, x22, [sp, #16]
    ldp     x19, x20, [sp], #96
    ret
    .size tinyshogi_a64fx_sdot_gemm_4x5, .-tinyshogi_a64fx_sdot_gemm_4x5

/* INT16 SDOT 4x5 tile.  This uses the same packed panel shape as the INT8
 * kernel, but each SDOT consumes four halfwords and accumulates into d lanes. */
    .align 6
    .global tinyshogi_a64fx_sdot_gemm_4x5_i16
    .type tinyshogi_a64fx_sdot_gemm_4x5_i16, %function
tinyshogi_a64fx_sdot_gemm_4x5_i16:
    stp     x19, x20, [sp, #-96]!
    stp     x21, x22, [sp, #16]
    stp     d8, d9, [sp, #32]
    stp     d10, d11, [sp, #48]
    stp     d12, d13, [sp, #64]
    stp     d14, d15, [sp, #80]
    ptrue   p0.b
    lsr     x19, x0, #2
    cbz     x19, .Lsdot16_done
    lsl     x20, x4, #3
    eor     z2.d, z2.d, z2.d
    eor     z3.d, z3.d, z3.d
    eor     z4.d, z4.d, z4.d
    eor     z5.d, z5.d, z5.d
    eor     z6.d, z6.d, z6.d
    eor     z7.d, z7.d, z7.d
    eor     z8.d, z8.d, z8.d
    eor     z9.d, z9.d, z9.d
    eor     z10.d, z10.d, z10.d
    eor     z11.d, z11.d, z11.d
    eor     z12.d, z12.d, z12.d
    eor     z13.d, z13.d, z13.d
    eor     z14.d, z14.d, z14.d
    eor     z15.d, z15.d, z15.d
    eor     z16.d, z16.d, z16.d
    eor     z17.d, z17.d, z17.d
    eor     z18.d, z18.d, z18.d
    eor     z19.d, z19.d, z19.d
    eor     z20.d, z20.d, z20.d
    eor     z21.d, z21.d, z21.d
    cmp     x19, #2
    b.lt    .Lsdot16_tail
    ld1rd   {z22.d}, p0/z, [x2]
    ld1rd   {z23.d}, p0/z, [x2, #8]
    ld1rd   {z24.d}, p0/z, [x2, #16]
    ld1rd   {z25.d}, p0/z, [x2, #24]
    ld1rd   {z26.d}, p0/z, [x2, #32]
    ld1rd   {z27.d}, p0/z, [x2, #40]
    ld1rd   {z28.d}, p0/z, [x2, #48]
    ld1h    {z0.h}, p0/z, [x1]

    .align 6
.Lsdot16_loop:
    ld1h    {z1.h}, p0/z, [x1, #1, mul vl]
    sdot z2.d,z0.h,z22.h
    sdot z3.d,z0.h,z23.h
    ld1rd {z29.d},p0/z,[x2,#56]
    ld1rd {z30.d},p0/z,[x2,#64]
    sdot z4.d,z0.h,z24.h
    sdot z5.d,z0.h,z25.h
    sdot z6.d,z0.h,z26.h
    sdot z7.d,z1.h,z22.h
    ld1h {z0.h},p0/z,[x1,#2,mul vl]
    ld1rd {z31.d},p0/z,[x2,#72]
    sdot z8.d,z1.h,z23.h
    sdot z9.d,z1.h,z24.h
    sdot z10.d,z1.h,z25.h
    sdot z11.d,z1.h,z26.h
    ld1h {z1.h},p0/z,[x1,#3,mul vl]
    sdot z12.d,z0.h,z22.h
    sdot z13.d,z0.h,z23.h
    sdot z14.d,z0.h,z24.h
    sdot z15.d,z0.h,z25.h
    sdot z16.d,z0.h,z26.h
    sdot z17.d,z1.h,z22.h
    ld1h {z0.h},p0/z,[x1,#4,mul vl]
    sdot z18.d,z1.h,z23.h
    sdot z19.d,z1.h,z24.h
    ld1rd {z22.d},p0/z,[x2,#80]
    ld1rd {z23.d},p0/z,[x2,#88]
    sdot z20.d,z1.h,z25.h
    sdot z21.d,z1.h,z26.h

    ld1h {z1.h},p0/z,[x1,#5,mul vl]
    sdot z2.d,z0.h,z27.h
    sdot z3.d,z0.h,z28.h
    ld1rd {z24.d},p0/z,[x2,#96]
    ld1rd {z25.d},p0/z,[x2,#104]
    sdot z4.d,z0.h,z29.h
    sdot z5.d,z0.h,z30.h
    sdot z6.d,z0.h,z31.h
    sdot z7.d,z1.h,z27.h
    ld1h {z0.h},p0/z,[x1,#6,mul vl]
    ld1rd {z26.d},p0/z,[x2,#112]
    sdot z8.d,z1.h,z28.h
    sdot z9.d,z1.h,z29.h
    sdot z10.d,z1.h,z30.h
    sdot z11.d,z1.h,z31.h
    ld1h {z1.h},p0/z,[x1,#7,mul vl]
    add x1,x1,#512
    sdot z12.d,z0.h,z27.h
    sdot z13.d,z0.h,z28.h
    sdot z14.d,z0.h,z29.h
    sdot z15.d,z0.h,z30.h
    sdot z16.d,z0.h,z31.h
    sdot z17.d,z1.h,z27.h
    ld1h {z0.h},p0/z,[x1]
    cmp x19,#4
    sdot z18.d,z1.h,z28.h
    sdot z19.d,z1.h,z29.h
    ld1rd {z27.d},p0/z,[x2,#120]
    ld1rd {z28.d},p0/z,[x2,#128]
    sdot z20.d,z1.h,z30.h
    sdot z21.d,z1.h,z31.h
    add x2,x2,#80
    sub x19,x19,#2
    b.ge .Lsdot16_loop

.Lsdot16_tail:
    cmp x19,#1
    b.lt .Lsdot16_store
    ld1h {z1.h},p0/z,[x1,#1,mul vl]
    sdot z2.d,z0.h,z22.h
    sdot z3.d,z0.h,z23.h
    sdot z4.d,z0.h,z24.h
    sdot z5.d,z0.h,z25.h
    sdot z6.d,z0.h,z26.h
    sdot z7.d,z1.h,z22.h
    ld1h {z0.h},p0/z,[x1,#2,mul vl]
    sdot z8.d,z1.h,z23.h
    sdot z9.d,z1.h,z24.h
    sdot z10.d,z1.h,z25.h
    sdot z11.d,z1.h,z26.h
    ld1h {z1.h},p0/z,[x1,#3,mul vl]
    sdot z12.d,z0.h,z22.h
    sdot z13.d,z0.h,z23.h
    sdot z14.d,z0.h,z24.h
    sdot z15.d,z0.h,z25.h
    sdot z16.d,z0.h,z26.h
    sdot z17.d,z1.h,z22.h
    sdot z18.d,z1.h,z23.h
    sdot z19.d,z1.h,z24.h
    sdot z20.d,z1.h,z25.h
    sdot z21.d,z1.h,z26.h

.Lsdot16_store:
    mov     x21, x3
    st1d    {z2.d}, p0, [x21]
    st1d    {z7.d}, p0, [x21, #1, mul vl]
    st1d    {z12.d}, p0, [x21, #2, mul vl]
    st1d    {z17.d}, p0, [x21, #3, mul vl]
    add     x21, x21, x20
    st1d    {z3.d}, p0, [x21]
    st1d    {z8.d}, p0, [x21, #1, mul vl]
    st1d    {z13.d}, p0, [x21, #2, mul vl]
    st1d    {z18.d}, p0, [x21, #3, mul vl]
    add     x21, x21, x20
    st1d    {z4.d}, p0, [x21]
    st1d    {z9.d}, p0, [x21, #1, mul vl]
    st1d    {z14.d}, p0, [x21, #2, mul vl]
    st1d    {z19.d}, p0, [x21, #3, mul vl]
    add     x21, x21, x20
    st1d    {z5.d}, p0, [x21]
    st1d    {z10.d}, p0, [x21, #1, mul vl]
    st1d    {z15.d}, p0, [x21, #2, mul vl]
    st1d    {z20.d}, p0, [x21, #3, mul vl]
    add     x21, x21, x20
    st1d    {z6.d}, p0, [x21]
    st1d    {z11.d}, p0, [x21, #1, mul vl]
    st1d    {z16.d}, p0, [x21, #2, mul vl]
    st1d    {z21.d}, p0, [x21, #3, mul vl]
.Lsdot16_done:
    ldp     d14, d15, [sp, #80]
    ldp     d12, d13, [sp, #64]
    ldp     d10, d11, [sp, #48]
    ldp     d8, d9, [sp, #32]
    ldp     x21, x22, [sp, #16]
    ldp     x19, x20, [sp], #96
    ret
    .size tinyshogi_a64fx_sdot_gemm_4x5_i16, .-tinyshogi_a64fx_sdot_gemm_4x5_i16
