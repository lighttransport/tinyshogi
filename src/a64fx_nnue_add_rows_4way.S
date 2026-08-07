/* Four-bank NNUE accumulator update.  Four independent accumulator banks
 * reduce the carried dependency distance to four feature rows. */
    .arch armv8.2-a+sve
    .text
    .align 6
    .global tinyshogi_nnue_add_i16_i32_rows_sve_4way
    .type tinyshogi_nnue_add_i16_i32_rows_sve_4way, %function
tinyshogi_nnue_add_i16_i32_rows_sve_4way:
    cbz     x2, .Lrows4_done
    ptrue   p0.s
    mov     x6, #0
    mov     x8, #0
.Lrows4_block:
    ld1w    {z0.s}, p0/z, [x0, #0, mul vl]
    ld1w    {z1.s}, p0/z, [x0, #1, mul vl]
    ld1w    {z2.s}, p0/z, [x0, #2, mul vl]
    ld1w    {z3.s}, p0/z, [x0, #3, mul vl]
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
    mov     x6, #0
    cmp     w4, #0
    b.lt    .Lrows4_sub
.Lrows4_add:
    add     x12, x6, #3
    cmp     x12, x2
    b.hs    .Lrows4_add_tail
    add     x13, x1, x6, lsl #3
    ldp     x7, x9, [x13]
    ldp     x10, x11, [x13, #16]
    add     x7, x7, x8
    add     x9, x9, x8
    add     x10, x10, x8
    add     x11, x11, x8
    ld1sh   {z16.s}, p0/z, [x7]
    ld1sh   {z17.s}, p0/z, [x7, #1, mul vl]
    ld1sh   {z18.s}, p0/z, [x7, #2, mul vl]
    ld1sh   {z19.s}, p0/z, [x7, #3, mul vl]
    ld1sh   {z20.s}, p0/z, [x9]
    ld1sh   {z21.s}, p0/z, [x9, #1, mul vl]
    ld1sh   {z22.s}, p0/z, [x9, #2, mul vl]
    ld1sh   {z23.s}, p0/z, [x9, #3, mul vl]
    ld1sh   {z24.s}, p0/z, [x10]
    ld1sh   {z25.s}, p0/z, [x10, #1, mul vl]
    ld1sh   {z26.s}, p0/z, [x10, #2, mul vl]
    ld1sh   {z27.s}, p0/z, [x10, #3, mul vl]
    ld1sh   {z28.s}, p0/z, [x11]
    ld1sh   {z29.s}, p0/z, [x11, #1, mul vl]
    ld1sh   {z30.s}, p0/z, [x11, #2, mul vl]
    ld1sh   {z31.s}, p0/z, [x11, #3, mul vl]
    add     z0.s, z0.s, z16.s
    add     z1.s, z1.s, z17.s
    add     z2.s, z2.s, z18.s
    add     z3.s, z3.s, z19.s
    add     z4.s, z4.s, z20.s
    add     z5.s, z5.s, z21.s
    add     z6.s, z6.s, z22.s
    add     z7.s, z7.s, z23.s
    add     z8.s, z8.s, z24.s
    add     z9.s, z9.s, z25.s
    add     z10.s, z10.s, z26.s
    add     z11.s, z11.s, z27.s
    add     z12.s, z12.s, z28.s
    add     z13.s, z13.s, z29.s
    add     z14.s, z14.s, z30.s
    add     z15.s, z15.s, z31.s
    add     x6, x6, #4
    b       .Lrows4_add
.Lrows4_add_tail:
    cmp     x6, x2
    b.hs    .Lrows4_reduce
    ldr     x7, [x1, x6, lsl #3]
    add     x7, x7, x8
    ld1sh   {z16.s}, p0/z, [x7]
    ld1sh   {z17.s}, p0/z, [x7, #1, mul vl]
    ld1sh   {z18.s}, p0/z, [x7, #2, mul vl]
    ld1sh   {z19.s}, p0/z, [x7, #3, mul vl]
    add     z0.s, z0.s, z16.s
    add     z1.s, z1.s, z17.s
    add     z2.s, z2.s, z18.s
    add     z3.s, z3.s, z19.s
    add     x6, x6, #1
    b       .Lrows4_add_tail
.Lrows4_sub:
    add     x12, x6, #3
    cmp     x12, x2
    b.hs    .Lrows4_sub_tail
    add     x13, x1, x6, lsl #3
    ldp     x7, x9, [x13]
    ldp     x10, x11, [x13, #16]
    add     x7, x7, x8
    add     x9, x9, x8
    add     x10, x10, x8
    add     x11, x11, x8
    ld1sh   {z16.s}, p0/z, [x7]
    ld1sh   {z17.s}, p0/z, [x7, #1, mul vl]
    ld1sh   {z18.s}, p0/z, [x7, #2, mul vl]
    ld1sh   {z19.s}, p0/z, [x7, #3, mul vl]
    ld1sh   {z20.s}, p0/z, [x9]
    ld1sh   {z21.s}, p0/z, [x9, #1, mul vl]
    ld1sh   {z22.s}, p0/z, [x9, #2, mul vl]
    ld1sh   {z23.s}, p0/z, [x9, #3, mul vl]
    ld1sh   {z24.s}, p0/z, [x10]
    ld1sh   {z25.s}, p0/z, [x10, #1, mul vl]
    ld1sh   {z26.s}, p0/z, [x10, #2, mul vl]
    ld1sh   {z27.s}, p0/z, [x10, #3, mul vl]
    ld1sh   {z28.s}, p0/z, [x11]
    ld1sh   {z29.s}, p0/z, [x11, #1, mul vl]
    ld1sh   {z30.s}, p0/z, [x11, #2, mul vl]
    ld1sh   {z31.s}, p0/z, [x11, #3, mul vl]
    sub     z0.s, z0.s, z16.s
    sub     z1.s, z1.s, z17.s
    sub     z2.s, z2.s, z18.s
    sub     z3.s, z3.s, z19.s
    sub     z4.s, z4.s, z20.s
    sub     z5.s, z5.s, z21.s
    sub     z6.s, z6.s, z22.s
    sub     z7.s, z7.s, z23.s
    sub     z8.s, z8.s, z24.s
    sub     z9.s, z9.s, z25.s
    sub     z10.s, z10.s, z26.s
    sub     z11.s, z11.s, z27.s
    sub     z12.s, z12.s, z28.s
    sub     z13.s, z13.s, z29.s
    sub     z14.s, z14.s, z30.s
    sub     z15.s, z15.s, z31.s
    add     x6, x6, #4
    b       .Lrows4_sub
.Lrows4_sub_tail:
    cmp     x6, x2
    b.hs    .Lrows4_reduce
    ldr     x7, [x1, x6, lsl #3]
    add     x7, x7, x8
    ld1sh   {z16.s}, p0/z, [x7]
    ld1sh   {z17.s}, p0/z, [x7, #1, mul vl]
    ld1sh   {z18.s}, p0/z, [x7, #2, mul vl]
    ld1sh   {z19.s}, p0/z, [x7, #3, mul vl]
    sub     z0.s, z0.s, z16.s
    sub     z1.s, z1.s, z17.s
    sub     z2.s, z2.s, z18.s
    sub     z3.s, z3.s, z19.s
    add     x6, x6, #1
    b       .Lrows4_sub_tail
.Lrows4_reduce:
    add     z0.s, z0.s, z4.s
    add     z0.s, z0.s, z8.s
    add     z0.s, z0.s, z12.s
    add     z1.s, z1.s, z5.s
    add     z1.s, z1.s, z9.s
    add     z1.s, z1.s, z13.s
    add     z2.s, z2.s, z6.s
    add     z2.s, z2.s, z10.s
    add     z2.s, z2.s, z14.s
    add     z3.s, z3.s, z7.s
    add     z3.s, z3.s, z11.s
    add     z3.s, z3.s, z15.s
    st1w    {z0.s}, p0, [x0, #0, mul vl]
    st1w    {z1.s}, p0, [x0, #1, mul vl]
    st1w    {z2.s}, p0, [x0, #2, mul vl]
    st1w    {z3.s}, p0, [x0, #3, mul vl]
    add     x0, x0, #256
    add     x8, x8, #128
    subs    x3, x3, #64
    b.ne    .Lrows4_block
.Lrows4_done:
    ret
    .size tinyshogi_nnue_add_i16_i32_rows_sve_4way, .-tinyshogi_nnue_add_i16_i32_rows_sve_4way
