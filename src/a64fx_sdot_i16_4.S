/* Four-output int16 SDOT dot product.  weights are four rows with stride
 * supplied in bytes; count is a multiple of 256. */
    .arch armv8.2-a+sve
    .text
    .align 6
    .global tinyshogi_dot_i16_i16_4_sve_sdot
    .type tinyshogi_dot_i16_i16_4_sve_sdot, %function
tinyshogi_dot_i16_i16_4_sve_sdot:
    ptrue   p0.b
    ptrue   p1.d
    lsl     x5, x2, #1
    mov     x10, x4
    add     x6, x1, x5
    add     x7, x6, x5
    add     x8, x7, x5
    dup     z16.d, #0
    dup     z17.d, #0
    dup     z18.d, #0
    dup     z19.d, #0
    mov     x9, #0
.Ldot4_256:
    ld1h    {z0.h}, p0/z, [x0, #0, mul vl]
    ld1h    {z1.h}, p0/z, [x1, #0, mul vl]
    ld1h    {z2.h}, p0/z, [x6, #0, mul vl]
    ld1h    {z3.h}, p0/z, [x7, #0, mul vl]
    ld1h    {z4.h}, p0/z, [x8, #0, mul vl]
    sdot    z16.d, z0.h, z1.h
    sdot    z17.d, z0.h, z2.h
    sdot    z18.d, z0.h, z3.h
    sdot    z19.d, z0.h, z4.h
    ld1h    {z0.h}, p0/z, [x0, #1, mul vl]
    ld1h    {z1.h}, p0/z, [x1, #1, mul vl]
    ld1h    {z2.h}, p0/z, [x6, #1, mul vl]
    ld1h    {z3.h}, p0/z, [x7, #1, mul vl]
    ld1h    {z4.h}, p0/z, [x8, #1, mul vl]
    sdot    z16.d, z0.h, z1.h
    sdot    z17.d, z0.h, z2.h
    sdot    z18.d, z0.h, z3.h
    sdot    z19.d, z0.h, z4.h
    ld1h    {z0.h}, p0/z, [x0, #2, mul vl]
    ld1h    {z1.h}, p0/z, [x1, #2, mul vl]
    ld1h    {z2.h}, p0/z, [x6, #2, mul vl]
    ld1h    {z3.h}, p0/z, [x7, #2, mul vl]
    ld1h    {z4.h}, p0/z, [x8, #2, mul vl]
    sdot    z16.d, z0.h, z1.h
    sdot    z17.d, z0.h, z2.h
    sdot    z18.d, z0.h, z3.h
    sdot    z19.d, z0.h, z4.h
    ld1h    {z0.h}, p0/z, [x0, #3, mul vl]
    ld1h    {z1.h}, p0/z, [x1, #3, mul vl]
    ld1h    {z2.h}, p0/z, [x6, #3, mul vl]
    ld1h    {z3.h}, p0/z, [x7, #3, mul vl]
    ld1h    {z4.h}, p0/z, [x8, #3, mul vl]
    sdot    z16.d, z0.h, z1.h
    sdot    z17.d, z0.h, z2.h
    sdot    z18.d, z0.h, z3.h
    sdot    z19.d, z0.h, z4.h
    ld1h    {z0.h}, p0/z, [x0, #4, mul vl]
    ld1h    {z1.h}, p0/z, [x1, #4, mul vl]
    ld1h    {z2.h}, p0/z, [x6, #4, mul vl]
    ld1h    {z3.h}, p0/z, [x7, #4, mul vl]
    ld1h    {z4.h}, p0/z, [x8, #4, mul vl]
    sdot    z16.d, z0.h, z1.h
    sdot    z17.d, z0.h, z2.h
    sdot    z18.d, z0.h, z3.h
    sdot    z19.d, z0.h, z4.h
    ld1h    {z0.h}, p0/z, [x0, #5, mul vl]
    ld1h    {z1.h}, p0/z, [x1, #5, mul vl]
    ld1h    {z2.h}, p0/z, [x6, #5, mul vl]
    ld1h    {z3.h}, p0/z, [x7, #5, mul vl]
    ld1h    {z4.h}, p0/z, [x8, #5, mul vl]
    sdot    z16.d, z0.h, z1.h
    sdot    z17.d, z0.h, z2.h
    sdot    z18.d, z0.h, z3.h
    sdot    z19.d, z0.h, z4.h
    ld1h    {z0.h}, p0/z, [x0, #6, mul vl]
    ld1h    {z1.h}, p0/z, [x1, #6, mul vl]
    ld1h    {z2.h}, p0/z, [x6, #6, mul vl]
    ld1h    {z3.h}, p0/z, [x7, #6, mul vl]
    ld1h    {z4.h}, p0/z, [x8, #6, mul vl]
    sdot    z16.d, z0.h, z1.h
    sdot    z17.d, z0.h, z2.h
    sdot    z18.d, z0.h, z3.h
    sdot    z19.d, z0.h, z4.h
    ld1h    {z0.h}, p0/z, [x0, #7, mul vl]
    ld1h    {z1.h}, p0/z, [x1, #7, mul vl]
    ld1h    {z2.h}, p0/z, [x6, #7, mul vl]
    ld1h    {z3.h}, p0/z, [x7, #7, mul vl]
    ld1h    {z4.h}, p0/z, [x8, #7, mul vl]
    sdot    z16.d, z0.h, z1.h
    sdot    z17.d, z0.h, z2.h
    sdot    z18.d, z0.h, z3.h
    sdot    z19.d, z0.h, z4.h
    add     x0, x0, #512
    add     x1, x1, #512
    add     x6, x6, #512
    add     x7, x7, #512
    add     x8, x8, #512
    add     x9, x9, #256
    cmp     x9, x3
    b.lo    .Ldot4_256
    uaddv   d0, p1, z16.d
    uaddv   d1, p1, z17.d
    uaddv   d2, p1, z18.d
    uaddv   d3, p1, z19.d
    fmov    x0, d0
    fmov    x1, d1
    fmov    x4, d2
    fmov    x5, d3
    stp     x0, x1, [x10]
    stp     x4, x5, [x10, #16]
    ret
    .size tinyshogi_dot_i16_i16_4_sve_sdot, .-tinyshogi_dot_i16_i16_4_sve_sdot
