/* Single-row NNUE accumulator update for the common incremental case. */
    .arch armv8.2-a+sve
    .text
    .align 6
    .global tinyshogi_nnue_add_i16_i32_one_sve
    .type tinyshogi_nnue_add_i16_i32_one_sve, %function
tinyshogi_nnue_add_i16_i32_one_sve:
    cbz     x2, .Lone_done
    ptrue   p0.s
    cmp     w3, #0
    b.lt    .Lone_sub
.Lone_add:
    ld1w    {z0.s}, p0/z, [x0, #0, mul vl]
    ld1w    {z1.s}, p0/z, [x0, #1, mul vl]
    ld1w    {z2.s}, p0/z, [x0, #2, mul vl]
    ld1w    {z3.s}, p0/z, [x0, #3, mul vl]
    ld1sh   {z4.s}, p0/z, [x1, #0, mul vl]
    ld1sh   {z5.s}, p0/z, [x1, #1, mul vl]
    ld1sh   {z6.s}, p0/z, [x1, #2, mul vl]
    ld1sh   {z7.s}, p0/z, [x1, #3, mul vl]
    add     z0.s, z0.s, z4.s
    add     z1.s, z1.s, z5.s
    add     z2.s, z2.s, z6.s
    add     z3.s, z3.s, z7.s
    st1w    {z0.s}, p0, [x0, #0, mul vl]
    st1w    {z1.s}, p0, [x0, #1, mul vl]
    st1w    {z2.s}, p0, [x0, #2, mul vl]
    st1w    {z3.s}, p0, [x0, #3, mul vl]
    add     x0, x0, #256
    add     x1, x1, #128
    subs    x2, x2, #64
    b.ne    .Lone_add
    ret
.Lone_sub:
    ld1w    {z0.s}, p0/z, [x0, #0, mul vl]
    ld1w    {z1.s}, p0/z, [x0, #1, mul vl]
    ld1w    {z2.s}, p0/z, [x0, #2, mul vl]
    ld1w    {z3.s}, p0/z, [x0, #3, mul vl]
    ld1sh   {z4.s}, p0/z, [x1, #0, mul vl]
    ld1sh   {z5.s}, p0/z, [x1, #1, mul vl]
    ld1sh   {z6.s}, p0/z, [x1, #2, mul vl]
    ld1sh   {z7.s}, p0/z, [x1, #3, mul vl]
    sub     z0.s, z0.s, z4.s
    sub     z1.s, z1.s, z5.s
    sub     z2.s, z2.s, z6.s
    sub     z3.s, z3.s, z7.s
    st1w    {z0.s}, p0, [x0, #0, mul vl]
    st1w    {z1.s}, p0, [x0, #1, mul vl]
    st1w    {z2.s}, p0, [x0, #2, mul vl]
    st1w    {z3.s}, p0, [x0, #3, mul vl]
    add     x0, x0, #256
    add     x1, x1, #128
    subs    x2, x2, #64
    b.ne    .Lone_sub
.Lone_done:
    ret
    .size tinyshogi_nnue_add_i16_i32_one_sve, .-tinyshogi_nnue_add_i16_i32_one_sve
