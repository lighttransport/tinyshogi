/* Exact four-row NNUE update with no row-count guards in the hot loop. */
    .arch armv8.2-a+sve
    .text
    .align 6
    .global tinyshogi_nnue_add_i16_i32_rows_sve_4exact
    .type tinyshogi_nnue_add_i16_i32_rows_sve_4exact, %function
tinyshogi_nnue_add_i16_i32_rows_sve_4exact:
    cbz     x2, .L4exact_done
    ptrue   p0.s
    mov     x8, #0
    cmp     w4, #0
    b.lt    .L4exact_sub
.L4exact_add:
    ldp     x7, x9, [x1]
    ldp     x10, x11, [x1, #16]
    add     x7, x7, x8
    add     x9, x9, x8
    add     x10, x10, x8
    add     x11, x11, x8
    ld1w    {z0.s}, p0/z, [x0, #0, mul vl]
    ld1w    {z1.s}, p0/z, [x0, #1, mul vl]
    ld1w    {z2.s}, p0/z, [x0, #2, mul vl]
    ld1w    {z3.s}, p0/z, [x0, #3, mul vl]
    ld1sh   {z4.s}, p0/z, [x7]
    ld1sh   {z5.s}, p0/z, [x7, #1, mul vl]
    add     z0.s, z0.s, z4.s
    add     z1.s, z1.s, z5.s
    ld1sh   {z6.s}, p0/z, [x7, #2, mul vl]
    ld1sh   {z7.s}, p0/z, [x7, #3, mul vl]
    add     z2.s, z2.s, z6.s
    add     z3.s, z3.s, z7.s
    ld1sh   {z4.s}, p0/z, [x9]
    ld1sh   {z5.s}, p0/z, [x9, #1, mul vl]
    add     z0.s, z0.s, z4.s
    add     z1.s, z1.s, z5.s
    ld1sh   {z6.s}, p0/z, [x9, #2, mul vl]
    ld1sh   {z7.s}, p0/z, [x9, #3, mul vl]
    add     z2.s, z2.s, z6.s
    add     z3.s, z3.s, z7.s
    ld1sh   {z4.s}, p0/z, [x10]
    ld1sh   {z5.s}, p0/z, [x10, #1, mul vl]
    add     z0.s, z0.s, z4.s
    add     z1.s, z1.s, z5.s
    ld1sh   {z6.s}, p0/z, [x10, #2, mul vl]
    ld1sh   {z7.s}, p0/z, [x10, #3, mul vl]
    add     z2.s, z2.s, z6.s
    add     z3.s, z3.s, z7.s
    ld1sh   {z4.s}, p0/z, [x11]
    ld1sh   {z5.s}, p0/z, [x11, #1, mul vl]
    add     z0.s, z0.s, z4.s
    add     z1.s, z1.s, z5.s
    ld1sh   {z6.s}, p0/z, [x11, #2, mul vl]
    ld1sh   {z7.s}, p0/z, [x11, #3, mul vl]
    add     z2.s, z2.s, z6.s
    add     z3.s, z3.s, z7.s
    st1w    {z0.s}, p0, [x0, #0, mul vl]
    st1w    {z1.s}, p0, [x0, #1, mul vl]
    st1w    {z2.s}, p0, [x0, #2, mul vl]
    st1w    {z3.s}, p0, [x0, #3, mul vl]
    add     x0, x0, #256
    add     x8, x8, #128
    subs    x3, x3, #64
    b.ne    .L4exact_add
    ret
.L4exact_sub:
    ldp     x7, x9, [x1]
    ldp     x10, x11, [x1, #16]
    add     x7, x7, x8
    add     x9, x9, x8
    add     x10, x10, x8
    add     x11, x11, x8
    ld1w    {z0.s}, p0/z, [x0, #0, mul vl]
    ld1w    {z1.s}, p0/z, [x0, #1, mul vl]
    ld1w    {z2.s}, p0/z, [x0, #2, mul vl]
    ld1w    {z3.s}, p0/z, [x0, #3, mul vl]
    ld1sh   {z4.s}, p0/z, [x7]
    ld1sh   {z5.s}, p0/z, [x7, #1, mul vl]
    sub     z0.s, z0.s, z4.s
    sub     z1.s, z1.s, z5.s
    ld1sh   {z6.s}, p0/z, [x7, #2, mul vl]
    ld1sh   {z7.s}, p0/z, [x7, #3, mul vl]
    sub     z2.s, z2.s, z6.s
    sub     z3.s, z3.s, z7.s
    ld1sh   {z4.s}, p0/z, [x9]
    ld1sh   {z5.s}, p0/z, [x9, #1, mul vl]
    sub     z0.s, z0.s, z4.s
    sub     z1.s, z1.s, z5.s
    ld1sh   {z6.s}, p0/z, [x9, #2, mul vl]
    ld1sh   {z7.s}, p0/z, [x9, #3, mul vl]
    sub     z2.s, z2.s, z6.s
    sub     z3.s, z3.s, z7.s
    ld1sh   {z4.s}, p0/z, [x10]
    ld1sh   {z5.s}, p0/z, [x10, #1, mul vl]
    sub     z0.s, z0.s, z4.s
    sub     z1.s, z1.s, z5.s
    ld1sh   {z6.s}, p0/z, [x10, #2, mul vl]
    ld1sh   {z7.s}, p0/z, [x10, #3, mul vl]
    sub     z2.s, z2.s, z6.s
    sub     z3.s, z3.s, z7.s
    ld1sh   {z4.s}, p0/z, [x11]
    ld1sh   {z5.s}, p0/z, [x11, #1, mul vl]
    sub     z0.s, z0.s, z4.s
    sub     z1.s, z1.s, z5.s
    ld1sh   {z6.s}, p0/z, [x11, #2, mul vl]
    ld1sh   {z7.s}, p0/z, [x11, #3, mul vl]
    sub     z2.s, z2.s, z6.s
    sub     z3.s, z3.s, z7.s
    st1w    {z0.s}, p0, [x0, #0, mul vl]
    st1w    {z1.s}, p0, [x0, #1, mul vl]
    st1w    {z2.s}, p0, [x0, #2, mul vl]
    st1w    {z3.s}, p0, [x0, #3, mul vl]
    add     x0, x0, #256
    add     x8, x8, #128
    subs    x3, x3, #64
    b.ne    .L4exact_sub
.L4exact_done:
    ret
    .size tinyshogi_nnue_add_i16_i32_rows_sve_4exact, .-tinyshogi_nnue_add_i16_i32_rows_sve_4exact
