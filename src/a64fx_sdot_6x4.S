/* A64FX SVE INT8 SDOT 6x4 tile, adapted from Clair's register-renaming
 * kernel_6x4_ooo.S.  A is [K/4][6][4] bytes, B is [K/4][4][64] bytes and
 * C is column-major [4][96] int32.  Six A broadcasts plus four B vectors
 * leave all 24 accumulators resident in the 32 SVE registers. */
    .arch armv8.2-a+sve
    .text
    .align 6
    .global tinyshogi_a64fx_sdot_gemm_6x4
    .type tinyshogi_a64fx_sdot_gemm_6x4, %function
tinyshogi_a64fx_sdot_gemm_6x4:
    stp     x19, x20, [sp, #-112]!
    stp     x21, x22, [sp, #16]
    stp     x23, x24, [sp, #32]
    stp     d8, d9, [sp, #48]
    stp     d10, d11, [sp, #64]
    stp     d12, d13, [sp, #80]
    stp     d14, d15, [sp, #96]
    ptrue   p0.b
    lsr     x19, x0, #2
    cbz     x19, .Lsdot64_done
    mov     x20, x1
    mov     x21, x2
    mov     x22, x3
    lsl     x23, x4, #2
    dup     z0.s, #0
    dup     z1.s, #0
    dup     z2.s, #0
    dup     z3.s, #0
    dup     z4.s, #0
    dup     z5.s, #0
    dup     z6.s, #0
    dup     z7.s, #0
    dup     z8.s, #0
    dup     z9.s, #0
    dup     z10.s, #0
    dup     z11.s, #0
    dup     z12.s, #0
    dup     z13.s, #0
    dup     z14.s, #0
    dup     z15.s, #0
    dup     z16.s, #0
    dup     z17.s, #0
    dup     z18.s, #0
    dup     z19.s, #0
    dup     z20.s, #0
    dup     z21.s, #0
    dup     z22.s, #0
    dup     z23.s, #0

    // Prologue: first A panel. Each scalar is replicated into all byte lanes.
    ld1rw   {z24.s}, p0/z, [x20, #0]
    ld1rw   {z25.s}, p0/z, [x20, #4]
    ld1rw   {z26.s}, p0/z, [x20, #8]
    ld1rw   {z27.s}, p0/z, [x20, #12]
    ld1rw   {z28.s}, p0/z, [x20, #16]
    ld1rw   {z29.s}, p0/z, [x20, #20]
    add     x20, x20, #24
    subs    x19, x19, #1
    cbz     x19, .Lsdot64_last

.Lsdot64_loop:
    ld1b    {z30.b}, p0/z, [x21, #0, mul vl]
    ld1b    {z31.b}, p0/z, [x21, #1, mul vl]
    sdot    z0.s, z24.b, z30.b
    sdot    z1.s, z24.b, z31.b
    sdot    z4.s, z25.b, z30.b
    sdot    z5.s, z25.b, z31.b
    sdot    z8.s, z26.b, z30.b
    sdot    z9.s, z26.b, z31.b
    sdot    z12.s, z27.b, z30.b
    sdot    z13.s, z27.b, z31.b
    sdot    z16.s, z28.b, z30.b
    sdot    z17.s, z28.b, z31.b
    sdot    z20.s, z29.b, z30.b
    sdot    z21.s, z29.b, z31.b
    ld1b    {z30.b}, p0/z, [x21, #2, mul vl]
    ld1b    {z31.b}, p0/z, [x21, #3, mul vl]
    sdot    z2.s, z24.b, z30.b
    sdot    z3.s, z24.b, z31.b
    ld1rw   {z24.s}, p0/z, [x20, #0]
    sdot    z6.s, z25.b, z30.b
    sdot    z7.s, z25.b, z31.b
    ld1rw   {z25.s}, p0/z, [x20, #4]
    sdot    z10.s, z26.b, z30.b
    sdot    z11.s, z26.b, z31.b
    ld1rw   {z26.s}, p0/z, [x20, #8]
    sdot    z14.s, z27.b, z30.b
    sdot    z15.s, z27.b, z31.b
    ld1rw   {z27.s}, p0/z, [x20, #12]
    sdot    z18.s, z28.b, z30.b
    sdot    z19.s, z28.b, z31.b
    ld1rw   {z28.s}, p0/z, [x20, #16]
    sdot    z22.s, z29.b, z30.b
    sdot    z23.s, z29.b, z31.b
    ld1rw   {z29.s}, p0/z, [x20, #20]
    add     x20, x20, #24
    add     x21, x21, #256
    subs    x19, x19, #1
    b.ne    .Lsdot64_loop

.Lsdot64_last:
    ld1b    {z30.b}, p0/z, [x21, #0, mul vl]
    ld1b    {z31.b}, p0/z, [x21, #1, mul vl]
    sdot    z0.s, z24.b, z30.b
    sdot    z1.s, z24.b, z31.b
    sdot    z4.s, z25.b, z30.b
    sdot    z5.s, z25.b, z31.b
    sdot    z8.s, z26.b, z30.b
    sdot    z9.s, z26.b, z31.b
    sdot    z12.s, z27.b, z30.b
    sdot    z13.s, z27.b, z31.b
    sdot    z16.s, z28.b, z30.b
    sdot    z17.s, z28.b, z31.b
    sdot    z20.s, z29.b, z30.b
    sdot    z21.s, z29.b, z31.b
    ld1b    {z30.b}, p0/z, [x21, #2, mul vl]
    ld1b    {z31.b}, p0/z, [x21, #3, mul vl]
    sdot    z2.s, z24.b, z30.b
    sdot    z3.s, z24.b, z31.b
    sdot    z6.s, z25.b, z30.b
    sdot    z7.s, z25.b, z31.b
    sdot    z10.s, z26.b, z30.b
    sdot    z11.s, z26.b, z31.b
    sdot    z14.s, z27.b, z30.b
    sdot    z15.s, z27.b, z31.b
    sdot    z18.s, z28.b, z30.b
    sdot    z19.s, z28.b, z31.b
    sdot    z22.s, z29.b, z30.b
    sdot    z23.s, z29.b, z31.b

    ptrue   p0.s
    st1w    {z0.s}, p0, [x22]
    st1w    {z1.s}, p0, [x22, #1, mul vl]
    st1w    {z2.s}, p0, [x22, #2, mul vl]
    st1w    {z3.s}, p0, [x22, #3, mul vl]
    add     x22, x22, x23
    st1w    {z4.s}, p0, [x22]
    st1w    {z5.s}, p0, [x22, #1, mul vl]
    st1w    {z6.s}, p0, [x22, #2, mul vl]
    st1w    {z7.s}, p0, [x22, #3, mul vl]
    add     x22, x22, x23
    st1w    {z8.s}, p0, [x22]
    st1w    {z9.s}, p0, [x22, #1, mul vl]
    st1w    {z10.s}, p0, [x22, #2, mul vl]
    st1w    {z11.s}, p0, [x22, #3, mul vl]
    add     x22, x22, x23
    st1w    {z12.s}, p0, [x22]
    st1w    {z13.s}, p0, [x22, #1, mul vl]
    st1w    {z14.s}, p0, [x22, #2, mul vl]
    st1w    {z15.s}, p0, [x22, #3, mul vl]
    add     x22, x22, x23
    st1w    {z16.s}, p0, [x22]
    st1w    {z17.s}, p0, [x22, #1, mul vl]
    st1w    {z18.s}, p0, [x22, #2, mul vl]
    st1w    {z19.s}, p0, [x22, #3, mul vl]
    add     x22, x22, x23
    st1w    {z20.s}, p0, [x22]
    st1w    {z21.s}, p0, [x22, #1, mul vl]
    st1w    {z22.s}, p0, [x22, #2, mul vl]
    st1w    {z23.s}, p0, [x22, #3, mul vl]
.Lsdot64_done:
    ldp     d14, d15, [sp, #96]
    ldp     d12, d13, [sp, #80]
    ldp     d10, d11, [sp, #64]
    ldp     d8, d9, [sp, #48]
    ldp     x23, x24, [sp, #32]
    ldp     x21, x22, [sp, #16]
    ldp     x19, x20, [sp], #112
    ret
    .size tinyshogi_a64fx_sdot_gemm_6x4, .-tinyshogi_a64fx_sdot_gemm_6x4
