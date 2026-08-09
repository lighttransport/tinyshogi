/* Eight-output int16 SDOT tile.  The row stride argument is in int16 elements. */
    .arch armv8.2-a+sve
    .text
    .align 6
    .global tinyshogi_dot_i16_i16_8_sve_sdot
    .type tinyshogi_dot_i16_i16_8_sve_sdot, %function
tinyshogi_dot_i16_i16_8_sve_sdot:
    ptrue   p0.b
    ptrue   p1.d
    lsl     x5, x2, #1
    mov     x10, x4
    add     x6, x1, x5
    add     x7, x6, x5
    add     x8, x7, x5
    add     x9, x8, x5
    add     x11, x9, x5
    add     x12, x11, x5
    add     x13, x12, x5
    dup     z16.d, #0
    dup     z17.d, #0
    dup     z18.d, #0
    dup     z19.d, #0
    dup     z20.d, #0
    dup     z21.d, #0
    dup     z22.d, #0
    dup     z23.d, #0
    mov     x14, #0
.macro SDOT8 off
    ld1h    {z0.h}, p0/z, [x0, \off, mul vl]
    ld1h    {z1.h}, p0/z, [x1, \off, mul vl]
    ld1h    {z2.h}, p0/z, [x6, \off, mul vl]
    ld1h    {z3.h}, p0/z, [x7, \off, mul vl]
    ld1h    {z4.h}, p0/z, [x8, \off, mul vl]
    ld1h    {z5.h}, p0/z, [x9, \off, mul vl]
    ld1h    {z6.h}, p0/z, [x11, \off, mul vl]
    ld1h    {z7.h}, p0/z, [x12, \off, mul vl]
    ld1h    {z8.h}, p0/z, [x13, \off, mul vl]
    sdot    z16.d, z0.h, z1.h
    sdot    z17.d, z0.h, z2.h
    sdot    z18.d, z0.h, z3.h
    sdot    z19.d, z0.h, z4.h
    sdot    z20.d, z0.h, z5.h
    sdot    z21.d, z0.h, z6.h
    sdot    z22.d, z0.h, z7.h
    sdot    z23.d, z0.h, z8.h
.endm
.Ldot8_256:
    SDOT8 #0
    SDOT8 #1
    SDOT8 #2
    SDOT8 #3
    SDOT8 #4
    SDOT8 #5
    SDOT8 #6
    SDOT8 #7
    add     x0, x0, #512
    add     x1, x1, #512
    add     x6, x6, #512
    add     x7, x7, #512
    add     x8, x8, #512
    add     x9, x9, #512
    add     x11, x11, #512
    add     x12, x12, #512
    add     x13, x13, #512
    add     x14, x14, #256
    cmp     x14, x3
    b.lo    .Ldot8_256
    uaddv   d0, p1, z16.d
    uaddv   d1, p1, z17.d
    uaddv   d2, p1, z18.d
    uaddv   d3, p1, z19.d
    uaddv   d4, p1, z20.d
    uaddv   d5, p1, z21.d
    uaddv   d6, p1, z22.d
    uaddv   d7, p1, z23.d
    fmov    x0, d0
    fmov    x1, d1
    fmov    x2, d2
    fmov    x3, d3
    fmov    x4, d4
    fmov    x5, d5
    fmov    x6, d6
    fmov    x7, d7
    stp     x0, x1, [x10]
    stp     x2, x3, [x10, #16]
    stp     x4, x5, [x10, #32]
    stp     x6, x7, [x10, #48]
    ret
    .size tinyshogi_dot_i16_i16_8_sve_sdot, .-tinyshogi_dot_i16_i16_8_sve_sdot
