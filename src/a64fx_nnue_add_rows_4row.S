/* Fixed four/five-row NNUE update.  One accumulator bank avoids the
 * zero/reduce overhead of the general four-bank schedule. */
    .arch armv8.2-a+sve
    .text
    .align 6
    .global tinyshogi_nnue_add_i16_i32_rows_sve_4row
    .type tinyshogi_nnue_add_i16_i32_rows_sve_4row, %function
tinyshogi_nnue_add_i16_i32_rows_sve_4row:
    cbz     x2, .L4row_done
    ptrue   p0.s
    mov     x8, #0
    cmp     w4, #0
    b.lt    .L4row_sub
.L4row_add_block:
    ld1w    {z0.s}, p0/z, [x0, #0, mul vl]
    ld1w    {z1.s}, p0/z, [x0, #1, mul vl]
    ld1w    {z2.s}, p0/z, [x0, #2, mul vl]
    ld1w    {z3.s}, p0/z, [x0, #3, mul vl]
    ldp     x7, x9, [x1]
    ldp     x10, x11, [x1, #16]
    add     x7, x7, x8
    add     x9, x9, x8
    add     x10, x10, x8
    add     x11, x11, x8
    ld1sh   {z4.s}, p0/z, [x7]
    ld1sh   {z5.s}, p0/z, [x7, #1, mul vl]
    ld1sh   {z6.s}, p0/z, [x7, #2, mul vl]
    ld1sh   {z7.s}, p0/z, [x7, #3, mul vl]
    add     z0.s, z0.s, z4.s
    add     z1.s, z1.s, z5.s
    add     z2.s, z2.s, z6.s
    add     z3.s, z3.s, z7.s
    ld1sh   {z4.s}, p0/z, [x9]
    ld1sh   {z5.s}, p0/z, [x9, #1, mul vl]
    ld1sh   {z6.s}, p0/z, [x9, #2, mul vl]
    ld1sh   {z7.s}, p0/z, [x9, #3, mul vl]
    add     z0.s, z0.s, z4.s
    add     z1.s, z1.s, z5.s
    add     z2.s, z2.s, z6.s
    add     z3.s, z3.s, z7.s
    ld1sh   {z4.s}, p0/z, [x10]
    ld1sh   {z5.s}, p0/z, [x10, #1, mul vl]
    ld1sh   {z6.s}, p0/z, [x10, #2, mul vl]
    ld1sh   {z7.s}, p0/z, [x10, #3, mul vl]
    add     z0.s, z0.s, z4.s
    add     z1.s, z1.s, z5.s
    add     z2.s, z2.s, z6.s
    add     z3.s, z3.s, z7.s
    ld1sh   {z4.s}, p0/z, [x11]
    ld1sh   {z5.s}, p0/z, [x11, #1, mul vl]
    ld1sh   {z6.s}, p0/z, [x11, #2, mul vl]
    ld1sh   {z7.s}, p0/z, [x11, #3, mul vl]
    add     z0.s, z0.s, z4.s
    add     z1.s, z1.s, z5.s
    add     z2.s, z2.s, z6.s
    add     z3.s, z3.s, z7.s
    cmp     w2, #4
    b.eq    .L4row_add_store
    ldr     x12, [x1, #32]
    add     x12, x12, x8
    ld1sh   {z4.s}, p0/z, [x12]
    ld1sh   {z5.s}, p0/z, [x12, #1, mul vl]
    ld1sh   {z6.s}, p0/z, [x12, #2, mul vl]
    ld1sh   {z7.s}, p0/z, [x12, #3, mul vl]
    add     z0.s, z0.s, z4.s
    add     z1.s, z1.s, z5.s
    add     z2.s, z2.s, z6.s
    add     z3.s, z3.s, z7.s
    cmp     w2, #5
    b.ls    .L4row_add_store
    ldr     x12, [x1, #40]
    add     x12, x12, x8
    ld1sh   {z4.s}, p0/z, [x12]
    ld1sh   {z5.s}, p0/z, [x12, #1, mul vl]
    ld1sh   {z6.s}, p0/z, [x12, #2, mul vl]
    ld1sh   {z7.s}, p0/z, [x12, #3, mul vl]
    add     z0.s, z0.s, z4.s
    add     z1.s, z1.s, z5.s
    add     z2.s, z2.s, z6.s
    add     z3.s, z3.s, z7.s
.L4row_add_more:
    cmp     w2, #6
    b.ls    .L4row_add_store
    ldr     x12, [x1, #48]
    add     x12, x12, x8
    ld1sh   {z4.s}, p0/z, [x12]
    ld1sh   {z5.s}, p0/z, [x12, #1, mul vl]
    ld1sh   {z6.s}, p0/z, [x12, #2, mul vl]
    ld1sh   {z7.s}, p0/z, [x12, #3, mul vl]
    add     z0.s, z0.s, z4.s
    add     z1.s, z1.s, z5.s
    add     z2.s, z2.s, z6.s
    add     z3.s, z3.s, z7.s
    cmp     w2, #7
    b.ls    .L4row_add_store
    ldr     x12, [x1, #56]
    add     x12, x12, x8
    ld1sh   {z4.s}, p0/z, [x12]
    ld1sh   {z5.s}, p0/z, [x12, #1, mul vl]
    ld1sh   {z6.s}, p0/z, [x12, #2, mul vl]
    ld1sh   {z7.s}, p0/z, [x12, #3, mul vl]
    add     z0.s, z0.s, z4.s
    add     z1.s, z1.s, z5.s
    add     z2.s, z2.s, z6.s
    add     z3.s, z3.s, z7.s
.L4row_add_store:
    st1w    {z0.s}, p0, [x0, #0, mul vl]
    st1w    {z1.s}, p0, [x0, #1, mul vl]
    st1w    {z2.s}, p0, [x0, #2, mul vl]
    st1w    {z3.s}, p0, [x0, #3, mul vl]
    add     x0, x0, #256
    add     x8, x8, #128
    subs    x3, x3, #64
    b.ne    .L4row_add_block
    ret
.L4row_sub:
    ld1w    {z0.s}, p0/z, [x0, #0, mul vl]
    ld1w    {z1.s}, p0/z, [x0, #1, mul vl]
    ld1w    {z2.s}, p0/z, [x0, #2, mul vl]
    ld1w    {z3.s}, p0/z, [x0, #3, mul vl]
    ldp     x7, x9, [x1]
    ldp     x10, x11, [x1, #16]
    add     x7, x7, x8
    add     x9, x9, x8
    add     x10, x10, x8
    add     x11, x11, x8
    ld1sh   {z4.s}, p0/z, [x7]
    ld1sh   {z5.s}, p0/z, [x7, #1, mul vl]
    ld1sh   {z6.s}, p0/z, [x7, #2, mul vl]
    ld1sh   {z7.s}, p0/z, [x7, #3, mul vl]
    sub     z0.s, z0.s, z4.s
    sub     z1.s, z1.s, z5.s
    sub     z2.s, z2.s, z6.s
    sub     z3.s, z3.s, z7.s
    ld1sh   {z4.s}, p0/z, [x9]
    ld1sh   {z5.s}, p0/z, [x9, #1, mul vl]
    ld1sh   {z6.s}, p0/z, [x9, #2, mul vl]
    ld1sh   {z7.s}, p0/z, [x9, #3, mul vl]
    sub     z0.s, z0.s, z4.s
    sub     z1.s, z1.s, z5.s
    sub     z2.s, z2.s, z6.s
    sub     z3.s, z3.s, z7.s
    ld1sh   {z4.s}, p0/z, [x10]
    ld1sh   {z5.s}, p0/z, [x10, #1, mul vl]
    ld1sh   {z6.s}, p0/z, [x10, #2, mul vl]
    ld1sh   {z7.s}, p0/z, [x10, #3, mul vl]
    sub     z0.s, z0.s, z4.s
    sub     z1.s, z1.s, z5.s
    sub     z2.s, z2.s, z6.s
    sub     z3.s, z3.s, z7.s
    ld1sh   {z4.s}, p0/z, [x11]
    ld1sh   {z5.s}, p0/z, [x11, #1, mul vl]
    ld1sh   {z6.s}, p0/z, [x11, #2, mul vl]
    ld1sh   {z7.s}, p0/z, [x11, #3, mul vl]
    sub     z0.s, z0.s, z4.s
    sub     z1.s, z1.s, z5.s
    sub     z2.s, z2.s, z6.s
    sub     z3.s, z3.s, z7.s
    cmp     w2, #4
    b.eq    .L4row_sub_store
    ldr     x12, [x1, #32]
    add     x12, x12, x8
    ld1sh   {z4.s}, p0/z, [x12]
    ld1sh   {z5.s}, p0/z, [x12, #1, mul vl]
    ld1sh   {z6.s}, p0/z, [x12, #2, mul vl]
    ld1sh   {z7.s}, p0/z, [x12, #3, mul vl]
    sub     z0.s, z0.s, z4.s
    sub     z1.s, z1.s, z5.s
    sub     z2.s, z2.s, z6.s
    sub     z3.s, z3.s, z7.s
    cmp     w2, #5
    b.ls    .L4row_sub_store
    ldr     x12, [x1, #40]
    add     x12, x12, x8
    ld1sh   {z4.s}, p0/z, [x12]
    ld1sh   {z5.s}, p0/z, [x12, #1, mul vl]
    ld1sh   {z6.s}, p0/z, [x12, #2, mul vl]
    ld1sh   {z7.s}, p0/z, [x12, #3, mul vl]
    sub     z0.s, z0.s, z4.s
    sub     z1.s, z1.s, z5.s
    sub     z2.s, z2.s, z6.s
    sub     z3.s, z3.s, z7.s
.L4row_sub_more:
    cmp     w2, #6
    b.ls    .L4row_sub_store
    ldr     x12, [x1, #48]
    add     x12, x12, x8
    ld1sh   {z4.s}, p0/z, [x12]
    ld1sh   {z5.s}, p0/z, [x12, #1, mul vl]
    ld1sh   {z6.s}, p0/z, [x12, #2, mul vl]
    ld1sh   {z7.s}, p0/z, [x12, #3, mul vl]
    sub     z0.s, z0.s, z4.s
    sub     z1.s, z1.s, z5.s
    sub     z2.s, z2.s, z6.s
    sub     z3.s, z3.s, z7.s
    cmp     w2, #7
    b.ls    .L4row_sub_store
    ldr     x12, [x1, #56]
    add     x12, x12, x8
    ld1sh   {z4.s}, p0/z, [x12]
    ld1sh   {z5.s}, p0/z, [x12, #1, mul vl]
    ld1sh   {z6.s}, p0/z, [x12, #2, mul vl]
    ld1sh   {z7.s}, p0/z, [x12, #3, mul vl]
    sub     z0.s, z0.s, z4.s
    sub     z1.s, z1.s, z5.s
    sub     z2.s, z2.s, z6.s
    sub     z3.s, z3.s, z7.s
.L4row_sub_store:
    st1w    {z0.s}, p0, [x0, #0, mul vl]
    st1w    {z1.s}, p0, [x0, #1, mul vl]
    st1w    {z2.s}, p0, [x0, #2, mul vl]
    st1w    {z3.s}, p0, [x0, #3, mul vl]
    add     x0, x0, #256
    add     x8, x8, #128
    subs    x3, x3, #64
    b.ne    .L4row_sub
.L4row_done:
    ret
    .size tinyshogi_nnue_add_i16_i32_rows_sve_4row, .-tinyshogi_nnue_add_i16_i32_rows_sve_4row
