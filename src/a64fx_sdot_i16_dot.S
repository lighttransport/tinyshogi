/* A64FX SVE int16 dot product with int64 accumulators.
 * Eight independent accumulators hide SDOT latency for 256-wide layers. */
    .arch armv8.2-a+sve
    .text
    .align 6
    .global tinyshogi_dot_i16_i16_sve_sdot
    .type tinyshogi_dot_i16_i16_sve_sdot, %function
tinyshogi_dot_i16_i16_sve_sdot:
    ptrue   p0.b
    ptrue   p1.d
    dup     z16.d, #0
    dup     z17.d, #0
    dup     z18.d, #0
    dup     z19.d, #0
    dup     z20.d, #0
    dup     z21.d, #0
    dup     z22.d, #0
    dup     z23.d, #0
    mov     x3, #0
.Ldot256:
    ld1h    {z0.h}, p0/z, [x0, #0, mul vl]
    ld1h    {z1.h}, p0/z, [x1, #0, mul vl]
    sdot    z16.d, z0.h, z1.h
    ld1h    {z0.h}, p0/z, [x0, #1, mul vl]
    ld1h    {z1.h}, p0/z, [x1, #1, mul vl]
    sdot    z17.d, z0.h, z1.h
    ld1h    {z0.h}, p0/z, [x0, #2, mul vl]
    ld1h    {z1.h}, p0/z, [x1, #2, mul vl]
    sdot    z18.d, z0.h, z1.h
    ld1h    {z0.h}, p0/z, [x0, #3, mul vl]
    ld1h    {z1.h}, p0/z, [x1, #3, mul vl]
    sdot    z19.d, z0.h, z1.h
    ld1h    {z0.h}, p0/z, [x0, #4, mul vl]
    ld1h    {z1.h}, p0/z, [x1, #4, mul vl]
    sdot    z20.d, z0.h, z1.h
    ld1h    {z0.h}, p0/z, [x0, #5, mul vl]
    ld1h    {z1.h}, p0/z, [x1, #5, mul vl]
    sdot    z21.d, z0.h, z1.h
    ld1h    {z0.h}, p0/z, [x0, #6, mul vl]
    ld1h    {z1.h}, p0/z, [x1, #6, mul vl]
    sdot    z22.d, z0.h, z1.h
    ld1h    {z0.h}, p0/z, [x0, #7, mul vl]
    ld1h    {z1.h}, p0/z, [x1, #7, mul vl]
    sdot    z23.d, z0.h, z1.h
    add     x0, x0, #512
    add     x1, x1, #512
    add     x3, x3, #256
    cmp     x3, x2
    b.lo    .Ldot256
    /* Reduce in registers: one 512-bit UADDV costs nine uops on A64FX. */
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
    .size tinyshogi_dot_i16_i16_sve_sdot, .-tinyshogi_dot_i16_i16_sve_sdot
