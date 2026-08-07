/* A64FX SVE INT16 SDOT 6x4 tile.  This is the 6-row register-renaming
 * schedule with ld1rd/ld1h and d-lane accumulators. */
    .arch armv8.2-a+sve
    .text
    .align 6
    .global tinyshogi_a64fx_sdot_gemm_6x4_i16
    .type tinyshogi_a64fx_sdot_gemm_6x4_i16, %function
tinyshogi_a64fx_sdot_gemm_6x4_i16:
    stp     x19, x20, [sp, #-48]!
    stp     x21, x22, [sp, #16]
    stp     x23, x24, [sp, #32]
    ptrue   p0.b
    lsr     x19, x0, #2
    cbz     x19, .Lsdot64i16_done
    mov     x20, x1
    mov     x21, x2
    mov     x22, x3
    lsl     x23, x4, #3
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
    ld1rd   {z24.d}, p0/z, [x20, #0]
    ld1rd   {z25.d}, p0/z, [x20, #8]
    ld1rd   {z26.d}, p0/z, [x20, #16]
    ld1rd   {z27.d}, p0/z, [x20, #24]
    ld1rd   {z28.d}, p0/z, [x20, #32]
    ld1rd   {z29.d}, p0/z, [x20, #40]
    add     x20, x20, #48
    subs    x19, x19, #1
    cbz     x19, .Lsdot64i16_last
.Lsdot64i16_loop:
    ld1h    {z30.h}, p0/z, [x21, #0, mul vl]
    ld1h    {z31.h}, p0/z, [x21, #1, mul vl]
    sdot    z0.d, z24.h, z30.h
    sdot    z1.d, z24.h, z31.h
    sdot    z4.d, z25.h, z30.h
    sdot    z5.d, z25.h, z31.h
    sdot    z8.d, z26.h, z30.h
    sdot    z9.d, z26.h, z31.h
    sdot    z12.d, z27.h, z30.h
    sdot    z13.d, z27.h, z31.h
    sdot    z16.d, z28.h, z30.h
    sdot    z17.d, z28.h, z31.h
    sdot    z20.d, z29.h, z30.h
    sdot    z21.d, z29.h, z31.h
    ld1h    {z30.h}, p0/z, [x21, #2, mul vl]
    ld1h    {z31.h}, p0/z, [x21, #3, mul vl]
    sdot    z2.d, z24.h, z30.h
    sdot    z3.d, z24.h, z31.h
    ld1rd   {z24.d}, p0/z, [x20, #0]
    sdot    z6.d, z25.h, z30.h
    sdot    z7.d, z25.h, z31.h
    ld1rd   {z25.d}, p0/z, [x20, #8]
    sdot    z10.d, z26.h, z30.h
    sdot    z11.d, z26.h, z31.h
    ld1rd   {z26.d}, p0/z, [x20, #16]
    sdot    z14.d, z27.h, z30.h
    sdot    z15.d, z27.h, z31.h
    ld1rd   {z27.d}, p0/z, [x20, #24]
    sdot    z18.d, z28.h, z30.h
    sdot    z19.d, z28.h, z31.h
    ld1rd   {z28.d}, p0/z, [x20, #32]
    sdot    z22.d, z29.h, z30.h
    sdot    z23.d, z29.h, z31.h
    ld1rd   {z29.d}, p0/z, [x20, #40]
    add     x20, x20, #48
    add     x21, x21, #256
    subs    x19, x19, #1
    b.ne    .Lsdot64i16_loop
.Lsdot64i16_last:
    ld1h    {z30.h}, p0/z, [x21, #0, mul vl]
    ld1h    {z31.h}, p0/z, [x21, #1, mul vl]
    sdot    z0.d, z24.h, z30.h
    sdot    z1.d, z24.h, z31.h
    sdot    z4.d, z25.h, z30.h
    sdot    z5.d, z25.h, z31.h
    sdot    z8.d, z26.h, z30.h
    sdot    z9.d, z26.h, z31.h
    sdot    z12.d, z27.h, z30.h
    sdot    z13.d, z27.h, z31.h
    sdot    z16.d, z28.h, z30.h
    sdot    z17.d, z28.h, z31.h
    sdot    z20.d, z29.h, z30.h
    sdot    z21.d, z29.h, z31.h
    ld1h    {z30.h}, p0/z, [x21, #2, mul vl]
    ld1h    {z31.h}, p0/z, [x21, #3, mul vl]
    sdot    z2.d, z24.h, z30.h
    sdot    z3.d, z24.h, z31.h
    sdot    z6.d, z25.h, z30.h
    sdot    z7.d, z25.h, z31.h
    sdot    z10.d, z26.h, z30.h
    sdot    z11.d, z26.h, z31.h
    sdot    z14.d, z27.h, z30.h
    sdot    z15.d, z27.h, z31.h
    sdot    z18.d, z28.h, z30.h
    sdot    z19.d, z28.h, z31.h
    sdot    z22.d, z29.h, z30.h
    sdot    z23.d, z29.h, z31.h
    ptrue   p0.d
    st1d    {z0.d}, p0, [x22]
    st1d    {z1.d}, p0, [x22, #1, mul vl]
    st1d    {z2.d}, p0, [x22, #2, mul vl]
    st1d    {z3.d}, p0, [x22, #3, mul vl]
    add     x22, x22, x23
    st1d    {z4.d}, p0, [x22]
    st1d    {z5.d}, p0, [x22, #1, mul vl]
    st1d    {z6.d}, p0, [x22, #2, mul vl]
    st1d    {z7.d}, p0, [x22, #3, mul vl]
    add     x22, x22, x23
    st1d    {z8.d}, p0, [x22]
    st1d    {z9.d}, p0, [x22, #1, mul vl]
    st1d    {z10.d}, p0, [x22, #2, mul vl]
    st1d    {z11.d}, p0, [x22, #3, mul vl]
    add     x22, x22, x23
    st1d    {z12.d}, p0, [x22]
    st1d    {z13.d}, p0, [x22, #1, mul vl]
    st1d    {z14.d}, p0, [x22, #2, mul vl]
    st1d    {z15.d}, p0, [x22, #3, mul vl]
    add     x22, x22, x23
    st1d    {z16.d}, p0, [x22]
    st1d    {z17.d}, p0, [x22, #1, mul vl]
    st1d    {z18.d}, p0, [x22, #2, mul vl]
    st1d    {z19.d}, p0, [x22, #3, mul vl]
    add     x22, x22, x23
    st1d    {z20.d}, p0, [x22]
    st1d    {z21.d}, p0, [x22, #1, mul vl]
    st1d    {z22.d}, p0, [x22, #2, mul vl]
    st1d    {z23.d}, p0, [x22, #3, mul vl]
.Lsdot64i16_done:
    ldp     x23, x24, [sp, #32]
    ldp     x21, x22, [sp, #16]
    ldp     x19, x20, [sp], #48
    ret
    .size tinyshogi_a64fx_sdot_gemm_6x4_i16, .-tinyshogi_a64fx_sdot_gemm_6x4_i16
