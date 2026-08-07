/* Add/subtract a bank of int16 NNUE feature rows into int32 accumulators.
 * A64FX SVE1 LD1SH supplies sign-extended words directly; four vectors are
 * kept live to hide the dependent accumulator update latency. */
    .arch armv8.2-a+sve
    .text
    .align 6
    .global tinyshogi_nnue_add_i16_i32_rows_sve
    .type tinyshogi_nnue_add_i16_i32_rows_sve, %function
tinyshogi_nnue_add_i16_i32_rows_sve:
    cbz     x2, .Lnnue_rows_done
    ptrue   p0.s
    mov     x5, #0
    mov     x6, #0
    mov     x8, #0
.Lnnue_rows_block:
    ld1w    {z0.s}, p0/z, [x0, #0, mul vl]
    ld1w    {z1.s}, p0/z, [x0, #1, mul vl]
    ld1w    {z2.s}, p0/z, [x0, #2, mul vl]
    ld1w    {z3.s}, p0/z, [x0, #3, mul vl]
    mov     x5, x1
    mov     x6, #0
.Lnnue_rows_row:
    ldr     x7, [x5, x6, lsl #3]
    add     x9, x7, x8
    ld1sh   {z4.s}, p0/z, [x9]
    add     x9, x9, #32
    ld1sh   {z5.s}, p0/z, [x9]
    add     x9, x9, #32
    ld1sh   {z6.s}, p0/z, [x9]
    add     x9, x9, #32
    ld1sh   {z7.s}, p0/z, [x9]
    cmp     w4, #0
    b.lt    .Lnnue_rows_sub
    add     z0.s, z0.s, z4.s
    add     z1.s, z1.s, z5.s
    add     z2.s, z2.s, z6.s
    add     z3.s, z3.s, z7.s
    b       .Lnnue_rows_next
.Lnnue_rows_sub:
    sub     z0.s, z0.s, z4.s
    sub     z1.s, z1.s, z5.s
    sub     z2.s, z2.s, z6.s
    sub     z3.s, z3.s, z7.s
.Lnnue_rows_next:
    add     x6, x6, #1
    cmp     x6, x2
    b.lo    .Lnnue_rows_row
    st1w    {z0.s}, p0, [x0, #0, mul vl]
    st1w    {z1.s}, p0, [x0, #1, mul vl]
    st1w    {z2.s}, p0, [x0, #2, mul vl]
    st1w    {z3.s}, p0, [x0, #3, mul vl]
    add     x0, x0, #256
    add     x8, x8, #128
    subs    x3, x3, #64
    b.ne    .Lnnue_rows_block
.Lnnue_rows_done:
    ret
    .size tinyshogi_nnue_add_i16_i32_rows_sve, .-tinyshogi_nnue_add_i16_i32_rows_sve
