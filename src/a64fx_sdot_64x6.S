/* A64FX INT8 SDOT tile: 64 output rows by six position columns.
 * A is packed [K/4][4][64] bytes, B is [K/4][6][4] bytes, and C is
 * row-major by position [6][ldc].  Twenty-four accumulators cover all
 * outputs; each four-byte position fragment is reused by four SVE vectors. */
    .arch armv8.2-a+sve
    .text
    .align 6
    .global tinyshogi_a64fx_sdot_gemm_64x6
    .type tinyshogi_a64fx_sdot_gemm_64x6, %function
tinyshogi_a64fx_sdot_gemm_64x6:
    stp     x19, x20, [sp, #-96]!
    stp     d8, d9, [sp, #16]
    stp     d10, d11, [sp, #32]
    stp     d12, d13, [sp, #48]
    stp     d14, d15, [sp, #64]
    str     x21, [sp, #80]
    ptrue   p0.b
    lsr     x19, x0, #2
    cbz     x19, .Lsdot64x6_done
    lsl     x20, x4, #2

    dup z0.s,#0
    dup z1.s,#0
    dup z2.s,#0
    dup z3.s,#0
    dup z4.s,#0
    dup z5.s,#0
    dup z6.s,#0
    dup z7.s,#0
    dup z8.s,#0
    dup z9.s,#0
    dup z10.s,#0
    dup z11.s,#0
    dup z12.s,#0
    dup z13.s,#0
    dup z14.s,#0
    dup z15.s,#0
    dup z16.s,#0
    dup z17.s,#0
    dup z18.s,#0
    dup z19.s,#0
    dup z20.s,#0
    dup z21.s,#0
    dup z22.s,#0
    dup z23.s,#0

    .align 6
.Lsdot64x6_loop:
    ld1b    {z24.b}, p0/z, [x1, #0, mul vl]
    ld1b    {z25.b}, p0/z, [x1, #1, mul vl]
    ld1rw   {z28.s}, p0/z, [x2, #0]
    sdot    z0.s, z24.b, z28.b
    sdot    z1.s, z25.b, z28.b
    ld1b    {z26.b}, p0/z, [x1, #2, mul vl]
    ld1b    {z27.b}, p0/z, [x1, #3, mul vl]
    sdot    z2.s, z26.b, z28.b
    sdot    z3.s, z27.b, z28.b

    ld1rw   {z28.s}, p0/z, [x2, #4]
    sdot    z4.s, z24.b, z28.b
    sdot    z5.s, z25.b, z28.b
    sdot    z6.s, z26.b, z28.b
    sdot    z7.s, z27.b, z28.b
    ld1rw   {z28.s}, p0/z, [x2, #8]
    sdot    z8.s, z24.b, z28.b
    sdot    z9.s, z25.b, z28.b
    sdot    z10.s, z26.b, z28.b
    sdot    z11.s, z27.b, z28.b
    ld1rw   {z28.s}, p0/z, [x2, #12]
    sdot    z12.s, z24.b, z28.b
    sdot    z13.s, z25.b, z28.b
    sdot    z14.s, z26.b, z28.b
    sdot    z15.s, z27.b, z28.b
    ld1rw   {z28.s}, p0/z, [x2, #16]
    sdot    z16.s, z24.b, z28.b
    sdot    z17.s, z25.b, z28.b
    sdot    z18.s, z26.b, z28.b
    sdot    z19.s, z27.b, z28.b
    ld1rw   {z28.s}, p0/z, [x2, #20]
    sdot    z20.s, z24.b, z28.b
    sdot    z21.s, z25.b, z28.b
    sdot    z22.s, z26.b, z28.b
    sdot    z23.s, z27.b, z28.b
    add     x1, x1, #256
    add     x2, x2, #24
    subs    x19, x19, #1
    b.ne    .Lsdot64x6_loop

    ptrue   p0.s
    mov     x21, x3
    st1w {z0.s},p0,[x21]
    st1w {z1.s},p0,[x21,#1,mul vl]
    st1w {z2.s},p0,[x21,#2,mul vl]
    st1w {z3.s},p0,[x21,#3,mul vl]
    add x21,x21,x20
    st1w {z4.s},p0,[x21]
    st1w {z5.s},p0,[x21,#1,mul vl]
    st1w {z6.s},p0,[x21,#2,mul vl]
    st1w {z7.s},p0,[x21,#3,mul vl]
    add x21,x21,x20
    st1w {z8.s},p0,[x21]
    st1w {z9.s},p0,[x21,#1,mul vl]
    st1w {z10.s},p0,[x21,#2,mul vl]
    st1w {z11.s},p0,[x21,#3,mul vl]
    add x21,x21,x20
    st1w {z12.s},p0,[x21]
    st1w {z13.s},p0,[x21,#1,mul vl]
    st1w {z14.s},p0,[x21,#2,mul vl]
    st1w {z15.s},p0,[x21,#3,mul vl]
    add x21,x21,x20
    st1w {z16.s},p0,[x21]
    st1w {z17.s},p0,[x21,#1,mul vl]
    st1w {z18.s},p0,[x21,#2,mul vl]
    st1w {z19.s},p0,[x21,#3,mul vl]
    add x21,x21,x20
    st1w {z20.s},p0,[x21]
    st1w {z21.s},p0,[x21,#1,mul vl]
    st1w {z22.s},p0,[x21,#2,mul vl]
    st1w {z23.s},p0,[x21,#3,mul vl]

.Lsdot64x6_done:
    ldr     x21, [sp, #80]
    ldp     d14, d15, [sp, #64]
    ldp     d12, d13, [sp, #48]
    ldp     d10, d11, [sp, #32]
    ldp     d8, d9, [sp, #16]
    ldp     x19, x20, [sp], #96
    ret
    .size tinyshogi_a64fx_sdot_gemm_64x6, .-tinyshogi_a64fx_sdot_gemm_64x6
