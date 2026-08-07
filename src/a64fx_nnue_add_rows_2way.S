/* Two-bank NNUE accumulator update.  Keep all live SVE registers below z16;
 * this also avoids the high-register LD1SH alias observed in QEMU's SVE path. */
    .arch armv8.2-a+sve
    .text
    .align 6
    .global tinyshogi_nnue_add_i16_i32_rows_sve_2way
    .type tinyshogi_nnue_add_i16_i32_rows_sve_2way, %function
tinyshogi_nnue_add_i16_i32_rows_sve_2way:
    cbz     x2, .Lrows2_done
    ptrue   p0.s
    mov     x6, #0
    mov     x8, #0
.Lrows2_block:
    ld1w    {z0.s}, p0/z, [x0, #0, mul vl]
    ld1w    {z1.s}, p0/z, [x0, #1, mul vl]
    ld1w    {z2.s}, p0/z, [x0, #2, mul vl]
    ld1w    {z3.s}, p0/z, [x0, #3, mul vl]
    dup     z4.s, #0
    dup     z5.s, #0
    dup     z6.s, #0
    dup     z7.s, #0
    mov     x6, #0
    cmp     w4, #0
    b.lt    .Lrows2_sub
.Lrows2_add:
    add     x10, x6, #1
    cmp     x10, x2
    b.hs    .Lrows2_add_tail
    ldr     x7, [x1, x6, lsl #3]
    ldr     x9, [x1, x10, lsl #3]
    add     x7, x7, x8
    add     x9, x9, x8
    ld1sh   {z8.s},  p0/z, [x7]
    add     x7, x7, #32
    ld1sh   {z9.s},  p0/z, [x7]
    add     x7, x7, #32
    ld1sh   {z10.s}, p0/z, [x7]
    add     x7, x7, #32
    ld1sh   {z11.s}, p0/z, [x7]
    ld1sh   {z12.s}, p0/z, [x9]
    add     x9, x9, #32
    ld1sh   {z13.s}, p0/z, [x9]
    add     x9, x9, #32
    ld1sh   {z14.s}, p0/z, [x9]
    add     x9, x9, #32
    ld1sh   {z15.s}, p0/z, [x9]
    add     z0.s, p0/m, z0.s, z8.s
    add     z1.s, p0/m, z1.s, z9.s
    add     z2.s, p0/m, z2.s, z10.s
    add     z3.s, p0/m, z3.s, z11.s
    add     z4.s, p0/m, z4.s, z12.s
    add     z5.s, p0/m, z5.s, z13.s
    add     z6.s, p0/m, z6.s, z14.s
    add     z7.s, p0/m, z7.s, z15.s
    add     x6, x6, #2
    b       .Lrows2_add
.Lrows2_add_tail:
    cmp     x6, x2
    b.hs    .Lrows2_reduce
    ldr     x7, [x1, x6, lsl #3]
    add     x7, x7, x8
    ld1sh   {z8.s},  p0/z, [x7]
    add     x7, x7, #32
    ld1sh   {z9.s},  p0/z, [x7]
    add     x7, x7, #32
    ld1sh   {z10.s}, p0/z, [x7]
    add     x7, x7, #32
    ld1sh   {z11.s}, p0/z, [x7]
    add     z0.s, p0/m, z0.s, z8.s
    add     z1.s, p0/m, z1.s, z9.s
    add     z2.s, p0/m, z2.s, z10.s
    add     z3.s, p0/m, z3.s, z11.s
    add     x6, x6, #1
    b       .Lrows2_add_tail
.Lrows2_sub:
    add     x10, x6, #1
    cmp     x10, x2
    b.hs    .Lrows2_sub_tail
    ldr     x7, [x1, x6, lsl #3]
    ldr     x9, [x1, x10, lsl #3]
    add     x7, x7, x8
    add     x9, x9, x8
    ld1sh   {z8.s},  p0/z, [x7]
    add     x7, x7, #32
    ld1sh   {z9.s},  p0/z, [x7]
    add     x7, x7, #32
    ld1sh   {z10.s}, p0/z, [x7]
    add     x7, x7, #32
    ld1sh   {z11.s}, p0/z, [x7]
    ld1sh   {z12.s}, p0/z, [x9]
    add     x9, x9, #32
    ld1sh   {z13.s}, p0/z, [x9]
    add     x9, x9, #32
    ld1sh   {z14.s}, p0/z, [x9]
    add     x9, x9, #32
    ld1sh   {z15.s}, p0/z, [x9]
    sub     z0.s, p0/m, z0.s, z8.s
    sub     z1.s, p0/m, z1.s, z9.s
    sub     z2.s, p0/m, z2.s, z10.s
    sub     z3.s, p0/m, z3.s, z11.s
    sub     z4.s, p0/m, z4.s, z12.s
    sub     z5.s, p0/m, z5.s, z13.s
    sub     z6.s, p0/m, z6.s, z14.s
    sub     z7.s, p0/m, z7.s, z15.s
    add     x6, x6, #2
    b       .Lrows2_sub
.Lrows2_sub_tail:
    cmp     x6, x2
    b.hs    .Lrows2_reduce
    ldr     x7, [x1, x6, lsl #3]
    add     x7, x7, x8
    ld1sh   {z8.s},  p0/z, [x7]
    add     x7, x7, #32
    ld1sh   {z9.s},  p0/z, [x7]
    add     x7, x7, #32
    ld1sh   {z10.s}, p0/z, [x7]
    add     x7, x7, #32
    ld1sh   {z11.s}, p0/z, [x7]
    sub     z0.s, p0/m, z0.s, z8.s
    sub     z1.s, p0/m, z1.s, z9.s
    sub     z2.s, p0/m, z2.s, z10.s
    sub     z3.s, p0/m, z3.s, z11.s
    add     x6, x6, #1
    b       .Lrows2_sub_tail
.Lrows2_reduce:
    add     z0.s, p0/m, z0.s, z4.s
    add     z1.s, p0/m, z1.s, z5.s
    add     z2.s, p0/m, z2.s, z6.s
    add     z3.s, p0/m, z3.s, z7.s
    st1w    {z0.s}, p0, [x0, #0, mul vl]
    st1w    {z1.s}, p0, [x0, #1, mul vl]
    st1w    {z2.s}, p0, [x0, #2, mul vl]
    st1w    {z3.s}, p0, [x0, #3, mul vl]
    add     x0, x0, #256
    add     x8, x8, #128
    subs    x3, x3, #64
    b.ne    .Lrows2_block
.Lrows2_done:
    ret
    .size tinyshogi_nnue_add_i16_i32_rows_sve_2way, .-tinyshogi_nnue_add_i16_i32_rows_sve_2way
