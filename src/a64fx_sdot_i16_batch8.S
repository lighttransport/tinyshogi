/* Eight-position NNUE output tile.
 * Each position has one shared INT16 weight vector.  Keeping eight output
 * accumulators live hides the nine-cycle SDOT latency and amortizes the
 * weight load across eight independent positions. */
    .arch armv8.2-a+sve
    .text
    .align 6
    .global tinyshogi_dot_i16_i16_batch8_sve_sdot
    .type tinyshogi_dot_i16_i16_batch8_sve_sdot, %function
tinyshogi_dot_i16_i16_batch8_sve_sdot:
    /* x0=positions, x1=stride (int16 elements), x2=weights,
     * x3=count (int16 elements), x4=output[8]. */
    cbz     x3, .Lbatch8_done
    ptrue   p0.b
    ptrue   p1.d
    lsl     x13, x1, #1
    mov     x5, x0
    add     x6, x0, x13
    add     x7, x6, x13
    add     x8, x7, x13
    add     x9, x8, x13
    add     x10, x9, x13
    add     x11, x10, x13
    add     x12, x11, x13
    dup     z16.d, #0
    dup     z17.d, #0
    dup     z18.d, #0
    dup     z19.d, #0
    dup     z20.d, #0
    dup     z21.d, #0
    dup     z22.d, #0
    dup     z23.d, #0

    .align 6
.Lbatch8_loop:
    ld1h    {z24.h}, p0/z, [x2]
    ld1h    {z0.h}, p0/z, [x5]
    ld1h    {z1.h}, p0/z, [x6]
    ld1h    {z2.h}, p0/z, [x7]
    ld1h    {z3.h}, p0/z, [x8]
    ld1h    {z4.h}, p0/z, [x9]
    ld1h    {z5.h}, p0/z, [x10]
    ld1h    {z6.h}, p0/z, [x11]
    ld1h    {z7.h}, p0/z, [x12]
    sdot    z16.d, z0.h, z24.h
    sdot    z17.d, z1.h, z24.h
    sdot    z18.d, z2.h, z24.h
    sdot    z19.d, z3.h, z24.h
    sdot    z20.d, z4.h, z24.h
    sdot    z21.d, z5.h, z24.h
    sdot    z22.d, z6.h, z24.h
    sdot    z23.d, z7.h, z24.h
    add     x2, x2, #64
    add     x5, x5, #64
    add     x6, x6, #64
    add     x7, x7, #64
    add     x8, x8, #64
    add     x9, x9, #64
    add     x10, x10, #64
    add     x11, x11, #64
    add     x12, x12, #64
    sub     x3, x3, #32
    cbnz    x3, .Lbatch8_loop

    uaddv   d0, p1, z16.d
    uaddv   d1, p1, z17.d
    uaddv   d2, p1, z18.d
    uaddv   d3, p1, z19.d
    uaddv   d4, p1, z20.d
    uaddv   d5, p1, z21.d
    uaddv   d6, p1, z22.d
    uaddv   d7, p1, z23.d
    fmov    x5, d0
    fmov    x6, d1
    fmov    x7, d2
    fmov    x8, d3
    fmov    x9, d4
    fmov    x10, d5
    fmov    x11, d6
    fmov    x12, d7
    stp     x5, x6, [x4, #0]
    stp     x7, x8, [x4, #16]
    stp     x9, x10, [x4, #32]
    stp     x11, x12, [x4, #48]
.Lbatch8_done:
    ret
    .size tinyshogi_dot_i16_i16_batch8_sve_sdot, .-tinyshogi_dot_i16_i16_batch8_sve_sdot
