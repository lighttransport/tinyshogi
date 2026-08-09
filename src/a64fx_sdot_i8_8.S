/* Eight-output int8 SDOT matrix-vector tile.  The row stride is in bytes. */
    .arch armv8.2-a+sve
    .text
    .align 6
    .global tinyshogi_dot_i8_i8_8_sve_sdot
    .type tinyshogi_dot_i8_i8_8_sve_sdot, %function
tinyshogi_dot_i8_i8_8_sve_sdot:
    ptrue   p0.b
    ptrue   p1.s
    mov     x10, x4
    add     x6, x1, x2
    add     x7, x6, x2
    add     x8, x7, x2
    add     x9, x8, x2
    add     x11, x9, x2
    add     x12, x11, x2
    add     x13, x12, x2
    dup     z16.s, #0
    dup     z17.s, #0
    dup     z18.s, #0
    dup     z19.s, #0
    dup     z20.s, #0
    dup     z21.s, #0
    dup     z22.s, #0
    dup     z23.s, #0
    mov     x14, #0
.macro SDOT8I off
    ld1b    {z0.b}, p0/z, [x0, \off, mul vl]
    ld1b    {z1.b}, p0/z, [x1, \off, mul vl]
    ld1b    {z2.b}, p0/z, [x6, \off, mul vl]
    ld1b    {z3.b}, p0/z, [x7, \off, mul vl]
    ld1b    {z4.b}, p0/z, [x8, \off, mul vl]
    ld1b    {z5.b}, p0/z, [x9, \off, mul vl]
    ld1b    {z6.b}, p0/z, [x11, \off, mul vl]
    ld1b    {z7.b}, p0/z, [x12, \off, mul vl]
    ld1b    {z8.b}, p0/z, [x13, \off, mul vl]
    sdot    z16.s, z0.b, z1.b
    sdot    z17.s, z0.b, z2.b
    sdot    z18.s, z0.b, z3.b
    sdot    z19.s, z0.b, z4.b
    sdot    z20.s, z0.b, z5.b
    sdot    z21.s, z0.b, z6.b
    sdot    z22.s, z0.b, z7.b
    sdot    z23.s, z0.b, z8.b
.endm
.Ldot8i_256:
    SDOT8I #0
    SDOT8I #1
    SDOT8I #2
    SDOT8I #3
    add     x0, x0, #256
    add     x1, x1, #256
    add     x6, x6, #256
    add     x7, x7, #256
    add     x8, x8, #256
    add     x9, x9, #256
    add     x11, x11, #256
    add     x12, x12, #256
    add     x13, x13, #256
    add     x14, x14, #256
    cmp     x14, x3
    b.lo    .Ldot8i_256
    uaddv   d0, p1, z16.s
    uaddv   d1, p1, z17.s
    uaddv   d2, p1, z18.s
    uaddv   d3, p1, z19.s
    uaddv   d4, p1, z20.s
    uaddv   d5, p1, z21.s
    uaddv   d6, p1, z22.s
    uaddv   d7, p1, z23.s
    fmov    x0, d0
    fmov    x1, d1
    fmov    x2, d2
    fmov    x3, d3
    fmov    x4, d4
    fmov    x5, d5
    fmov    x6, d6
    fmov    x7, d7
    stp     w0, w1, [x10]
    stp     w2, w3, [x10, #8]
    stp     w4, w5, [x10, #16]
    stp     w6, w7, [x10, #24]
    ret
    .size tinyshogi_dot_i8_i8_8_sve_sdot, .-tinyshogi_dot_i8_i8_8_sve_sdot
