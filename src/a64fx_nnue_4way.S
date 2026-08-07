/* Compact A64FX SVE1 NNUE dot/relu kernel.  Four independent accumulators
 * keep the body below the A64FX short-loop/decode threshold. */
    .arch armv8.2-a+sve
    .text
    .align 6
    .global tinyshogi_nnue_dot_relu_i32_i16_sve_4way
    .type tinyshogi_nnue_dot_relu_i32_i16_sve_4way, %function
tinyshogi_nnue_dot_relu_i32_i16_sve_4way:
    ptrue   p0.s
    ptrue   p1.d
    dup     z16.d, #0
    dup     z17.d, #0
    dup     z18.d, #0
    dup     z19.d, #0
    mov     x3, x0
    mov     x4, x1
    mov     x5, #0
.Lnnue64:
    ld1w    {z0.s}, p0/z, [x3, #0, mul vl]
    ld1sh   {z1.s}, p0/z, [x4, #0, mul vl]
    ld1w    {z2.s}, p0/z, [x3, #1, mul vl]
    ld1sh   {z3.s}, p0/z, [x4, #1, mul vl]
    smax    z0.s, z0.s, #0
    mul     z0.s, p0/m, z0.s, z1.s
    sunpklo z8.d, z0.s
    sunpkhi z9.d, z0.s
    add     z16.d, z16.d, z8.d
    add     z17.d, z17.d, z9.d

    ld1w    {z4.s}, p0/z, [x3, #2, mul vl]
    ld1sh   {z5.s}, p0/z, [x4, #2, mul vl]
    smax    z2.s, z2.s, #0
    mul     z2.s, p0/m, z2.s, z3.s
    sunpklo z10.d, z2.s
    sunpkhi z11.d, z2.s
    add     z18.d, z18.d, z10.d
    add     z19.d, z19.d, z11.d

    ld1w    {z6.s}, p0/z, [x3, #3, mul vl]
    ld1sh   {z7.s}, p0/z, [x4, #3, mul vl]
    smax    z4.s, z4.s, #0
    mul     z4.s, p0/m, z4.s, z5.s
    sunpklo z8.d, z4.s
    sunpkhi z9.d, z4.s
    add     z16.d, z16.d, z8.d
    add     z17.d, z17.d, z9.d

    smax    z6.s, z6.s, #0
    mul     z6.s, p0/m, z6.s, z7.s
    sunpklo z10.d, z6.s
    sunpkhi z11.d, z6.s
    add     z18.d, z18.d, z10.d
    add     z19.d, z19.d, z11.d
    add     x3, x3, #256
    add     x4, x4, #128
    add     x5, x5, #64
    cmp     x5, x2
    b.lo    .Lnnue64
    uaddv   d0, p1, z16.d
    uaddv   d1, p1, z17.d
    uaddv   d2, p1, z18.d
    uaddv   d3, p1, z19.d
    fmov    x0, d0
    fmov    x6, d1
    add     x0, x0, x6
    fmov    x6, d2
    add     x0, x0, x6
    fmov    x6, d3
    add     x0, x0, x6
    ret
    .size tinyshogi_nnue_dot_relu_i32_i16_sve_4way, .-tinyshogi_nnue_dot_relu_i32_i16_sve_4way
