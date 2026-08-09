/* A64FX SVE int16 SDOT form of the NNUE ReLU dot product.
 * The caller guarantees that all positive int32 activations fit in int16.
 * Negative activations are clamped to zero before packing. */
    .arch armv8.2-a+sve
    .text
    .align 6
    .global tinyshogi_nnue_dot_relu_i32_i16_sve_sdot
    .type tinyshogi_nnue_dot_relu_i32_i16_sve_sdot, %function
tinyshogi_nnue_dot_relu_i32_i16_sve_sdot:
    mov     x3, #32767
    b       .Lnnueclip_common
    .global tinyshogi_nnue_dot_clip_i32_i16_sve_sdot
    .type tinyshogi_nnue_dot_clip_i32_i16_sve_sdot, %function
tinyshogi_nnue_dot_clip_i32_i16_sve_sdot:
.Lnnueclip_common:
    ptrue   p0.b
    ptrue   p1.d
    ptrue   p2.s
    dup     z16.d, #0
    dup     z17.d, #0
    dup     z18.d, #0
    dup     z19.d, #0
    dup     z20.d, #0
    dup     z21.d, #0
    dup     z22.d, #0
    dup     z23.d, #0
    mov     x4, #0
.Lnnuesdot256:
    /* Load the complete 256-element tile before consuming it.  A64FX SVE
     * loads have eleven-cycle latency; sixteen independent loads expose
     * enough work for the out-of-order window to cover it. */
    add     x5, x0, #512
    dup     z24.s, w3
    ld1w    {z0.s}, p0/z, [x0, #0, mul vl]
    ld1w    {z1.s}, p0/z, [x0, #1, mul vl]
    ld1w    {z2.s}, p0/z, [x0, #2, mul vl]
    ld1w    {z3.s}, p0/z, [x0, #3, mul vl]
    ld1w    {z4.s}, p0/z, [x0, #4, mul vl]
    ld1w    {z5.s}, p0/z, [x0, #5, mul vl]
    ld1w    {z6.s}, p0/z, [x0, #6, mul vl]
    ld1w    {z7.s}, p0/z, [x0, #7, mul vl]
    ld1w    {z8.s}, p0/z, [x5, #0, mul vl]
    ld1w    {z9.s}, p0/z, [x5, #1, mul vl]
    ld1w    {z10.s}, p0/z, [x5, #2, mul vl]
    ld1w    {z11.s}, p0/z, [x5, #3, mul vl]
    ld1w    {z12.s}, p0/z, [x5, #4, mul vl]
    ld1w    {z13.s}, p0/z, [x5, #5, mul vl]
    ld1w    {z14.s}, p0/z, [x5, #6, mul vl]
    ld1w    {z15.s}, p0/z, [x5, #7, mul vl]
    smax    z0.s, z0.s, #0
    smax    z1.s, z1.s, #0
    smax    z2.s, z2.s, #0
    smax    z3.s, z3.s, #0
    smax    z4.s, z4.s, #0
    smax    z5.s, z5.s, #0
    smax    z6.s, z6.s, #0
    smax    z7.s, z7.s, #0
    smax    z8.s, z8.s, #0
    smax    z9.s, z9.s, #0
    smax    z10.s, z10.s, #0
    smax    z11.s, z11.s, #0
    smax    z12.s, z12.s, #0
    smax    z13.s, z13.s, #0
    smax    z14.s, z14.s, #0
    smax    z15.s, z15.s, #0
    smin    z0.s, p2/m, z0.s, z24.s
    smin    z1.s, p2/m, z1.s, z24.s
    smin    z2.s, p2/m, z2.s, z24.s
    smin    z3.s, p2/m, z3.s, z24.s
    smin    z4.s, p2/m, z4.s, z24.s
    smin    z5.s, p2/m, z5.s, z24.s
    smin    z6.s, p2/m, z6.s, z24.s
    smin    z7.s, p2/m, z7.s, z24.s
    smin    z8.s, p2/m, z8.s, z24.s
    smin    z9.s, p2/m, z9.s, z24.s
    smin    z10.s, p2/m, z10.s, z24.s
    smin    z11.s, p2/m, z11.s, z24.s
    smin    z12.s, p2/m, z12.s, z24.s
    smin    z13.s, p2/m, z13.s, z24.s
    smin    z14.s, p2/m, z14.s, z24.s
    smin    z15.s, p2/m, z15.s, z24.s
    /* The clip vector is dead after SMIN, so z24-z31 become the weight bank. */
    ld1h    {z24.h}, p0/z, [x1, #0, mul vl]
    ld1h    {z25.h}, p0/z, [x1, #1, mul vl]
    ld1h    {z26.h}, p0/z, [x1, #2, mul vl]
    ld1h    {z27.h}, p0/z, [x1, #3, mul vl]
    ld1h    {z28.h}, p0/z, [x1, #4, mul vl]
    ld1h    {z29.h}, p0/z, [x1, #5, mul vl]
    ld1h    {z30.h}, p0/z, [x1, #6, mul vl]
    ld1h    {z31.h}, p0/z, [x1, #7, mul vl]
    uzp1    z0.h, z0.h, z1.h
    uzp1    z2.h, z2.h, z3.h
    uzp1    z4.h, z4.h, z5.h
    uzp1    z6.h, z6.h, z7.h
    uzp1    z8.h, z8.h, z9.h
    uzp1    z10.h, z10.h, z11.h
    uzp1    z12.h, z12.h, z13.h
    uzp1    z14.h, z14.h, z15.h
    add     x0, x0, #1024
    add     x1, x1, #512
    sdot    z16.d, z0.h, z24.h
    sdot    z17.d, z2.h, z25.h
    sdot    z18.d, z4.h, z26.h
    sdot    z19.d, z6.h, z27.h
    sdot    z20.d, z8.h, z28.h
    sdot    z21.d, z10.h, z29.h
    sdot    z22.d, z12.h, z30.h
    sdot    z23.d, z14.h, z31.h
    add     x4, x4, #256
    cmp     x4, x2
    b.lo    .Lnnuesdot256
    /* A 512-bit UADDV is nine uops on A64FX.  Reduce the eight independent
     * SDOT accumulators as vectors first, then pay for one horizontal sum. */
    add     z16.d, z16.d, z17.d
    add     z18.d, z18.d, z19.d
    add     z20.d, z20.d, z21.d
    add     z22.d, z22.d, z23.d
    add     z16.d, z16.d, z18.d
    add     z20.d, z20.d, z22.d
    add     z16.d, z16.d, z20.d
    uaddv   d0, p1, z16.d
    fmov    x0, d0
    ret
    .size tinyshogi_nnue_dot_clip_i32_i16_sve_sdot, .-tinyshogi_nnue_dot_clip_i32_i16_sve_sdot
    .size tinyshogi_nnue_dot_relu_i32_i16_sve_sdot, .-tinyshogi_nnue_dot_relu_i32_i16_sve_sdot
