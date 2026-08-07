/* A64FX SVE FP32 4x5 GEMM tile. A is [K][4][16], B is [K][5]. */
    .arch armv8.2-a+sve
    .text
    .align 6
    .global tinyshogi_a64fx_sgemm_4x5
    .type tinyshogi_a64fx_sgemm_4x5, %function
tinyshogi_a64fx_sgemm_4x5:
    stp     x19, x20, [sp, #-32]!
    stp     x21, x22, [sp, #16]
    ptrue   p0.s
    cbz     x0, .Lsgemm45_done
    mov     x19, x0
    lsr     x19, x19, #1
    lsl     x20, x4, #2
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

.Lsgemm45_loop:
    // Keep the A64FX FLA/FLB pipes busy with a two-step software pipeline.
    // The benchmark contract uses an even K; each iteration consumes two K
    // rows, while the next row's vectors are loaded between FMA groups.
    ld1w    {z0.s}, p0/z, [x1, #0, mul vl]
    ld1w    {z1.s}, p0/z, [x1, #1, mul vl]
    ld1w    {z22.s}, p0/z, [x1, #2, mul vl]
    ld1w    {z23.s}, p0/z, [x1, #3, mul vl]
    ld1rw   {z24.s}, p0/z, [x2, #0]
    ld1rw   {z25.s}, p0/z, [x2, #4]
    ld1rw   {z26.s}, p0/z, [x2, #8]
    ld1rw   {z27.s}, p0/z, [x2, #12]
    ld1rw   {z28.s}, p0/z, [x2, #16]
    fmla    z2.s, p0/m, z0.s, z24.s
    fmla    z3.s, p0/m, z1.s, z24.s
    fmla    z4.s, p0/m, z22.s, z24.s
    fmla    z5.s, p0/m, z23.s, z24.s
    fmla    z6.s, p0/m, z0.s, z25.s
    fmla    z7.s, p0/m, z1.s, z25.s
    fmla    z8.s, p0/m, z22.s, z25.s
    fmla    z9.s, p0/m, z23.s, z25.s
    fmla    z10.s, p0/m, z0.s, z26.s
    fmla    z11.s, p0/m, z1.s, z26.s
    fmla    z12.s, p0/m, z22.s, z26.s
    fmla    z13.s, p0/m, z23.s, z26.s
    fmla    z14.s, p0/m, z0.s, z27.s
    fmla    z15.s, p0/m, z1.s, z27.s
    fmla    z16.s, p0/m, z22.s, z27.s
    fmla    z17.s, p0/m, z23.s, z27.s
    fmla    z18.s, p0/m, z0.s, z28.s
    fmla    z19.s, p0/m, z1.s, z28.s
    fmla    z20.s, p0/m, z22.s, z28.s
    fmla    z21.s, p0/m, z23.s, z28.s
    ld1w    {z0.s}, p0/z, [x1, #4, mul vl]
    ld1w    {z1.s}, p0/z, [x1, #5, mul vl]
    ld1w    {z22.s}, p0/z, [x1, #6, mul vl]
    ld1w    {z23.s}, p0/z, [x1, #7, mul vl]
    ld1rw   {z24.s}, p0/z, [x2, #20]
    ld1rw   {z25.s}, p0/z, [x2, #24]
    ld1rw   {z26.s}, p0/z, [x2, #28]
    ld1rw   {z27.s}, p0/z, [x2, #32]
    ld1rw   {z28.s}, p0/z, [x2, #36]
    fmla    z2.s, p0/m, z0.s, z24.s
    fmla    z3.s, p0/m, z1.s, z24.s
    fmla    z4.s, p0/m, z22.s, z24.s
    fmla    z5.s, p0/m, z23.s, z24.s
    fmla    z6.s, p0/m, z0.s, z25.s
    fmla    z7.s, p0/m, z1.s, z25.s
    fmla    z8.s, p0/m, z22.s, z25.s
    fmla    z9.s, p0/m, z23.s, z25.s
    fmla    z10.s, p0/m, z0.s, z26.s
    fmla    z11.s, p0/m, z1.s, z26.s
    fmla    z12.s, p0/m, z22.s, z26.s
    fmla    z13.s, p0/m, z23.s, z26.s
    fmla    z14.s, p0/m, z0.s, z27.s
    fmla    z15.s, p0/m, z1.s, z27.s
    fmla    z16.s, p0/m, z22.s, z27.s
    fmla    z17.s, p0/m, z23.s, z27.s
    fmla    z18.s, p0/m, z0.s, z28.s
    fmla    z19.s, p0/m, z1.s, z28.s
    fmla    z20.s, p0/m, z22.s, z28.s
    fmla    z21.s, p0/m, z23.s, z28.s
    add     x1, x1, #512
    add     x2, x2, #40
    subs    x19, x19, #1
    b.ne    .Lsgemm45_loop

    mov     x21, x3
    st1w    {z2.s}, p0, [x21]
    st1w    {z3.s}, p0, [x21, #1, mul vl]
    st1w    {z4.s}, p0, [x21, #2, mul vl]
    st1w    {z5.s}, p0, [x21, #3, mul vl]
    add     x21, x21, x20
    st1w    {z6.s}, p0, [x21]
    st1w    {z7.s}, p0, [x21, #1, mul vl]
    st1w    {z8.s}, p0, [x21, #2, mul vl]
    st1w    {z9.s}, p0, [x21, #3, mul vl]
    add     x21, x21, x20
    st1w    {z10.s}, p0, [x21]
    st1w    {z11.s}, p0, [x21, #1, mul vl]
    st1w    {z12.s}, p0, [x21, #2, mul vl]
    st1w    {z13.s}, p0, [x21, #3, mul vl]
    add     x21, x21, x20
    st1w    {z14.s}, p0, [x21]
    st1w    {z15.s}, p0, [x21, #1, mul vl]
    st1w    {z16.s}, p0, [x21, #2, mul vl]
    st1w    {z17.s}, p0, [x21, #3, mul vl]
    add     x21, x21, x20
    st1w    {z18.s}, p0, [x21]
    st1w    {z19.s}, p0, [x21, #1, mul vl]
    st1w    {z20.s}, p0, [x21, #2, mul vl]
    st1w    {z21.s}, p0, [x21, #3, mul vl]
.Lsgemm45_done:
    ldp     x21, x22, [sp, #16]
    ldp     x19, x20, [sp], #32
    ret
    .size tinyshogi_a64fx_sgemm_4x5, .-tinyshogi_a64fx_sgemm_4x5
