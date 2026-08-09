// FP32 SGEMM microkernel for A64FX SVE (512-bit)
// Tile: 3 SVE vectors (48 rows) x 8 columns = 24 accumulators
// Optimized: interleaved loads/FMAs, K-loop unrolled 2x, software prefetch
//
// void sgemm_kernel_3x8(int64_t K,           // x0
//                        const float *A,       // x1 (packed 48xK, 48 contiguous per K)
//                        const float *B,       // x2 (packed Kx8, 8 contiguous per K)
//                        float *C,             // x3 (column-major, stride ldc)
//                        int64_t ldc);         // x4 (in elements)
//
// Register allocation:
//   z0-z23:  24 accumulators (col j, panel p -> z[j*3+p])
//   z24-z26: A panel loads (rows 0-15, 16-31, 32-47)
//   z27-z31: B scalar broadcasts (double-buffered)
//   p0:      all-true predicate (.s)
//
// Accumulator layout (column-major):
//   col0: z0,  z1,  z2     col4: z12, z13, z14
//   col1: z3,  z4,  z5     col5: z15, z16, z17
//   col2: z6,  z7,  z8     col6: z18, z19, z20
//   col3: z9,  z10, z11    col7: z21, z22, z23
//
// Pipeline analysis (A64FX, per K-step):
//   24 FMAs on 2 FLA/FLB pipes = 12 cycles (bottleneck)
//   11 loads on 2 LD pipes = 5.5 cycles
//   Theoretical efficiency: 100% FMA utilization

    .arch armv8.2-a+sve
    .text
    .align 2
    .global tinyshogi_a64fx_sgemm_3x8
    .type tinyshogi_a64fx_sgemm_3x8, %function

tinyshogi_a64fx_sgemm_3x8:
    // Prologue: save callee-saved registers
    stp     x19, x20, [sp, #-80]!
    stp     x21, x22, [sp, #16]
    stp     d8, d9, [sp, #32]
    stp     d10, d11, [sp, #48]
    stp     d12, d13, [sp, #64]

    // Set up all-true predicate for 32-bit elements
    ptrue   p0.s

    // Precompute C column byte offsets: ldc * sizeof(float) = ldc * 4
    lsl     x5, x4, #2             // x5 = ldc * 4 bytes (col stride)
    lsl     x6, x5, #1             // x6 = ldc * 8  (col 2 offset)
    add     x7, x6, x5             // x7 = ldc * 12 (col 3 offset)
    lsl     x8, x5, #2             // x8 = ldc * 16 (col 4 offset)
    add     x9, x8, x5             // x9 = ldc * 20 (col 5 offset)
    add     x10, x8, x6            // x10 = ldc * 24 (col 6 offset)
    add     x11, x8, x7            // x11 = ldc * 28 (col 7 offset)

    // A stride per K step = MR * 4 = 48 * 4 = 192 bytes
    mov     x15, #192
    // B stride per K step = NR * 4 = 8 * 4 = 32 bytes
    mov     x16, #32

    // Zero all 24 accumulators
    fmov    z0.s, #0.0
    fmov    z1.s, #0.0
    fmov    z2.s, #0.0
    fmov    z3.s, #0.0
    fmov    z4.s, #0.0
    fmov    z5.s, #0.0
    fmov    z6.s, #0.0
    fmov    z7.s, #0.0
    fmov    z8.s, #0.0
    fmov    z9.s, #0.0
    fmov    z10.s, #0.0
    fmov    z11.s, #0.0
    fmov    z12.s, #0.0
    fmov    z13.s, #0.0
    fmov    z14.s, #0.0
    fmov    z15.s, #0.0
    fmov    z16.s, #0.0
    fmov    z17.s, #0.0
    fmov    z18.s, #0.0
    fmov    z19.s, #0.0
    fmov    z20.s, #0.0
    fmov    z21.s, #0.0
    fmov    z22.s, #0.0
    fmov    z23.s, #0.0

    // Check K > 0
    cmp     x0, #0
    ble     .Lstore

    // Save K for remainder check
    mov     x19, x0

    // Prefetch first A and B blocks
    prfm    pldl1keep, [x1]
    prfm    pldl1keep, [x1, #256]
    prfm    pldl1keep, [x2]
    prfm    pldl1keep, [x2, #256]

    // Main K-loop (unrolled 2x)
    lsr     x20, x0, #1            // x20 = K / 2
    cbz     x20, .Lk_remainder

    // Pre-load first A panel and B broadcasts for software pipelining
    ld1w    {z24.s}, p0/z, [x1, #0, mul vl]
    ld1w    {z25.s}, p0/z, [x1, #1, mul vl]
    ld1w    {z26.s}, p0/z, [x1, #2, mul vl]
    ld1rw   {z27.s}, p0/z, [x2]
    ld1rw   {z28.s}, p0/z, [x2, #4]

    subs    x20, x20, #1
    beq     .Lk_loop_2x_epilogue

    .align 4
.Lk_loop_2x:
    // ======== K-step 0 (interleaved schedule) ========
    // Loads for cols 2-4 interleaved with FMAs for cols 0-1

    ld1rw   {z29.s}, p0/z, [x2, #8]        // B[k,2]
    fmla    z0.s, p0/m, z24.s, z27.s        // col0 p0
    fmla    z1.s, p0/m, z25.s, z27.s        // col0 p1
    ld1rw   {z30.s}, p0/z, [x2, #12]       // B[k,3]
    fmla    z2.s, p0/m, z26.s, z27.s        // col0 p2
    fmla    z3.s, p0/m, z24.s, z28.s        // col1 p0
    ld1rw   {z31.s}, p0/z, [x2, #16]       // B[k,4]
    fmla    z4.s, p0/m, z25.s, z28.s        // col1 p1
    fmla    z5.s, p0/m, z26.s, z28.s        // col1 p2

    // FMAs for cols 2-4, interleave loads for cols 5-7
    fmla    z6.s, p0/m, z24.s, z29.s        // col2 p0
    ld1rw   {z27.s}, p0/z, [x2, #20]       // B[k,5] (reuse z27)
    fmla    z7.s, p0/m, z25.s, z29.s        // col2 p1
    fmla    z8.s, p0/m, z26.s, z29.s        // col2 p2
    ld1rw   {z28.s}, p0/z, [x2, #24]       // B[k,6] (reuse z28)
    fmla    z9.s, p0/m, z24.s, z30.s        // col3 p0
    fmla    z10.s, p0/m, z25.s, z30.s       // col3 p1
    ld1rw   {z29.s}, p0/z, [x2, #28]       // B[k,7] (reuse z29)
    fmla    z11.s, p0/m, z26.s, z30.s       // col3 p2
    fmla    z12.s, p0/m, z24.s, z31.s       // col4 p0

    // Prefetch ahead for A (next 2 K-steps = +384 bytes)
    prfm    pldl1keep, [x1, #384]

    fmla    z13.s, p0/m, z25.s, z31.s       // col4 p1
    fmla    z14.s, p0/m, z26.s, z31.s       // col4 p2

    // FMAs for cols 5-7, advance A ptr, start loading next A
    fmla    z15.s, p0/m, z24.s, z27.s       // col5 p0
    fmla    z16.s, p0/m, z25.s, z27.s       // col5 p1
    fmla    z17.s, p0/m, z26.s, z27.s       // col5 p2
    add     x1, x1, x15                     // A += 192
    fmla    z18.s, p0/m, z24.s, z28.s       // col6 p0
    fmla    z19.s, p0/m, z25.s, z28.s       // col6 p1
    fmla    z20.s, p0/m, z26.s, z28.s       // col6 p2
    add     x2, x2, x16                     // B += 32
    fmla    z21.s, p0/m, z24.s, z29.s       // col7 p0
    fmla    z22.s, p0/m, z25.s, z29.s       // col7 p1
    fmla    z23.s, p0/m, z26.s, z29.s       // col7 p2

    // ======== K-step 1 (interleaved schedule) ========

    // Load next A panel
    ld1w    {z24.s}, p0/z, [x1, #0, mul vl]
    ld1w    {z25.s}, p0/z, [x1, #1, mul vl]
    ld1w    {z26.s}, p0/z, [x1, #2, mul vl]

    // Load B[k+1, 0..1]
    ld1rw   {z27.s}, p0/z, [x2]
    ld1rw   {z28.s}, p0/z, [x2, #4]

    ld1rw   {z29.s}, p0/z, [x2, #8]        // B[k+1,2]
    fmla    z0.s, p0/m, z24.s, z27.s
    fmla    z1.s, p0/m, z25.s, z27.s
    ld1rw   {z30.s}, p0/z, [x2, #12]
    fmla    z2.s, p0/m, z26.s, z27.s
    fmla    z3.s, p0/m, z24.s, z28.s
    ld1rw   {z31.s}, p0/z, [x2, #16]
    fmla    z4.s, p0/m, z25.s, z28.s
    fmla    z5.s, p0/m, z26.s, z28.s

    fmla    z6.s, p0/m, z24.s, z29.s
    ld1rw   {z27.s}, p0/z, [x2, #20]
    fmla    z7.s, p0/m, z25.s, z29.s
    fmla    z8.s, p0/m, z26.s, z29.s
    ld1rw   {z28.s}, p0/z, [x2, #24]
    fmla    z9.s, p0/m, z24.s, z30.s
    fmla    z10.s, p0/m, z25.s, z30.s
    ld1rw   {z29.s}, p0/z, [x2, #28]
    fmla    z11.s, p0/m, z26.s, z30.s
    fmla    z12.s, p0/m, z24.s, z31.s

    // Prefetch ahead for B
    prfm    pldl1keep, [x2, #256]

    fmla    z13.s, p0/m, z25.s, z31.s
    fmla    z14.s, p0/m, z26.s, z31.s

    fmla    z15.s, p0/m, z24.s, z27.s
    fmla    z16.s, p0/m, z25.s, z27.s
    fmla    z17.s, p0/m, z26.s, z27.s
    add     x1, x1, x15
    fmla    z18.s, p0/m, z24.s, z28.s
    fmla    z19.s, p0/m, z25.s, z28.s
    fmla    z20.s, p0/m, z26.s, z28.s
    add     x2, x2, x16
    fmla    z21.s, p0/m, z24.s, z29.s
    fmla    z22.s, p0/m, z25.s, z29.s
    fmla    z23.s, p0/m, z26.s, z29.s

    // Re-load A and B[0:1] for next iteration (software pipeline)
    ld1w    {z24.s}, p0/z, [x1, #0, mul vl]
    ld1w    {z25.s}, p0/z, [x1, #1, mul vl]
    ld1w    {z26.s}, p0/z, [x1, #2, mul vl]
    ld1rw   {z27.s}, p0/z, [x2]
    ld1rw   {z28.s}, p0/z, [x2, #4]

    subs    x20, x20, #1
    bne     .Lk_loop_2x

.Lk_loop_2x_epilogue:
    // Process the last 2 K-steps (A/B already pre-loaded)

    // K-step 0
    ld1rw   {z29.s}, p0/z, [x2, #8]
    fmla    z0.s, p0/m, z24.s, z27.s
    fmla    z1.s, p0/m, z25.s, z27.s
    ld1rw   {z30.s}, p0/z, [x2, #12]
    fmla    z2.s, p0/m, z26.s, z27.s
    fmla    z3.s, p0/m, z24.s, z28.s
    ld1rw   {z31.s}, p0/z, [x2, #16]
    fmla    z4.s, p0/m, z25.s, z28.s
    fmla    z5.s, p0/m, z26.s, z28.s

    fmla    z6.s, p0/m, z24.s, z29.s
    ld1rw   {z27.s}, p0/z, [x2, #20]
    fmla    z7.s, p0/m, z25.s, z29.s
    fmla    z8.s, p0/m, z26.s, z29.s
    ld1rw   {z28.s}, p0/z, [x2, #24]
    fmla    z9.s, p0/m, z24.s, z30.s
    fmla    z10.s, p0/m, z25.s, z30.s
    ld1rw   {z29.s}, p0/z, [x2, #28]
    fmla    z11.s, p0/m, z26.s, z30.s
    fmla    z12.s, p0/m, z24.s, z31.s
    fmla    z13.s, p0/m, z25.s, z31.s
    fmla    z14.s, p0/m, z26.s, z31.s

    fmla    z15.s, p0/m, z24.s, z27.s
    fmla    z16.s, p0/m, z25.s, z27.s
    fmla    z17.s, p0/m, z26.s, z27.s
    add     x1, x1, x15
    fmla    z18.s, p0/m, z24.s, z28.s
    fmla    z19.s, p0/m, z25.s, z28.s
    fmla    z20.s, p0/m, z26.s, z28.s
    add     x2, x2, x16
    fmla    z21.s, p0/m, z24.s, z29.s
    fmla    z22.s, p0/m, z25.s, z29.s
    fmla    z23.s, p0/m, z26.s, z29.s

    // K-step 1
    ld1w    {z24.s}, p0/z, [x1, #0, mul vl]
    ld1w    {z25.s}, p0/z, [x1, #1, mul vl]
    ld1w    {z26.s}, p0/z, [x1, #2, mul vl]

    ld1rw   {z27.s}, p0/z, [x2]
    ld1rw   {z28.s}, p0/z, [x2, #4]
    ld1rw   {z29.s}, p0/z, [x2, #8]
    ld1rw   {z30.s}, p0/z, [x2, #12]
    ld1rw   {z31.s}, p0/z, [x2, #16]

    fmla    z0.s, p0/m, z24.s, z27.s
    fmla    z1.s, p0/m, z25.s, z27.s
    fmla    z2.s, p0/m, z26.s, z27.s
    fmla    z3.s, p0/m, z24.s, z28.s
    fmla    z4.s, p0/m, z25.s, z28.s
    fmla    z5.s, p0/m, z26.s, z28.s
    fmla    z6.s, p0/m, z24.s, z29.s
    fmla    z7.s, p0/m, z25.s, z29.s
    fmla    z8.s, p0/m, z26.s, z29.s
    fmla    z9.s, p0/m, z24.s, z30.s
    fmla    z10.s, p0/m, z25.s, z30.s
    fmla    z11.s, p0/m, z26.s, z30.s
    fmla    z12.s, p0/m, z24.s, z31.s
    fmla    z13.s, p0/m, z25.s, z31.s
    fmla    z14.s, p0/m, z26.s, z31.s

    ld1rw   {z27.s}, p0/z, [x2, #20]
    ld1rw   {z28.s}, p0/z, [x2, #24]
    ld1rw   {z29.s}, p0/z, [x2, #28]

    fmla    z15.s, p0/m, z24.s, z27.s
    fmla    z16.s, p0/m, z25.s, z27.s
    fmla    z17.s, p0/m, z26.s, z27.s
    fmla    z18.s, p0/m, z24.s, z28.s
    fmla    z19.s, p0/m, z25.s, z28.s
    fmla    z20.s, p0/m, z26.s, z28.s
    fmla    z21.s, p0/m, z24.s, z29.s
    fmla    z22.s, p0/m, z25.s, z29.s
    fmla    z23.s, p0/m, z26.s, z29.s

    b       .Lk_check_remainder

.Lk_remainder:
    // Handle odd K (K & 1)
    tst     x19, #1
    beq     .Lstore

    // Single K-step (no interleaving needed — only 1 iteration)
    ld1w    {z24.s}, p0/z, [x1, #0, mul vl]
    ld1w    {z25.s}, p0/z, [x1, #1, mul vl]
    ld1w    {z26.s}, p0/z, [x1, #2, mul vl]

    ld1rw   {z27.s}, p0/z, [x2]
    ld1rw   {z28.s}, p0/z, [x2, #4]
    ld1rw   {z29.s}, p0/z, [x2, #8]
    ld1rw   {z30.s}, p0/z, [x2, #12]
    ld1rw   {z31.s}, p0/z, [x2, #16]

    fmla    z0.s, p0/m, z24.s, z27.s
    fmla    z1.s, p0/m, z25.s, z27.s
    fmla    z2.s, p0/m, z26.s, z27.s
    fmla    z3.s, p0/m, z24.s, z28.s
    fmla    z4.s, p0/m, z25.s, z28.s
    fmla    z5.s, p0/m, z26.s, z28.s
    fmla    z6.s, p0/m, z24.s, z29.s
    fmla    z7.s, p0/m, z25.s, z29.s
    fmla    z8.s, p0/m, z26.s, z29.s
    fmla    z9.s, p0/m, z24.s, z30.s
    fmla    z10.s, p0/m, z25.s, z30.s
    fmla    z11.s, p0/m, z26.s, z30.s
    fmla    z12.s, p0/m, z24.s, z31.s
    fmla    z13.s, p0/m, z25.s, z31.s
    fmla    z14.s, p0/m, z26.s, z31.s

    ld1rw   {z27.s}, p0/z, [x2, #20]
    ld1rw   {z28.s}, p0/z, [x2, #24]
    ld1rw   {z29.s}, p0/z, [x2, #28]

    fmla    z15.s, p0/m, z24.s, z27.s
    fmla    z16.s, p0/m, z25.s, z27.s
    fmla    z17.s, p0/m, z26.s, z27.s
    fmla    z18.s, p0/m, z24.s, z28.s
    fmla    z19.s, p0/m, z25.s, z28.s
    fmla    z20.s, p0/m, z26.s, z28.s
    fmla    z21.s, p0/m, z24.s, z29.s
    fmla    z22.s, p0/m, z25.s, z29.s
    fmla    z23.s, p0/m, z26.s, z29.s

    b       .Lstore

.Lk_check_remainder:
    tst     x19, #1
    beq     .Lstore
    // Advance pointers past the 2x epilogue
    add     x1, x1, x15
    add     x2, x2, x16
    b       .Lk_remainder

.Lstore:
    // Store C columns (column-major, stride ldc)
    // col 0: C + 0
    st1w    {z0.s}, p0, [x3]
    add     x12, x3, #64
    st1w    {z1.s}, p0, [x12]
    add     x12, x12, #64
    st1w    {z2.s}, p0, [x12]

    // col 1: C + ldc*4
    add     x12, x3, x5
    st1w    {z3.s}, p0, [x12]
    add     x13, x12, #64
    st1w    {z4.s}, p0, [x13]
    add     x13, x13, #64
    st1w    {z5.s}, p0, [x13]

    // col 2: C + ldc*8
    add     x12, x3, x6
    st1w    {z6.s}, p0, [x12]
    add     x13, x12, #64
    st1w    {z7.s}, p0, [x13]
    add     x13, x13, #64
    st1w    {z8.s}, p0, [x13]

    // col 3: C + ldc*12
    add     x12, x3, x7
    st1w    {z9.s}, p0, [x12]
    add     x13, x12, #64
    st1w    {z10.s}, p0, [x13]
    add     x13, x13, #64
    st1w    {z11.s}, p0, [x13]

    // col 4: C + ldc*16
    add     x12, x3, x8
    st1w    {z12.s}, p0, [x12]
    add     x13, x12, #64
    st1w    {z13.s}, p0, [x13]
    add     x13, x13, #64
    st1w    {z14.s}, p0, [x13]

    // col 5: C + ldc*20
    add     x12, x3, x9
    st1w    {z15.s}, p0, [x12]
    add     x13, x12, #64
    st1w    {z16.s}, p0, [x13]
    add     x13, x13, #64
    st1w    {z17.s}, p0, [x13]

    // col 6: C + ldc*24
    add     x12, x3, x10
    st1w    {z18.s}, p0, [x12]
    add     x13, x12, #64
    st1w    {z19.s}, p0, [x13]
    add     x13, x13, #64
    st1w    {z20.s}, p0, [x13]

    // col 7: C + ldc*28
    add     x12, x3, x11
    st1w    {z21.s}, p0, [x12]
    add     x13, x12, #64
    st1w    {z22.s}, p0, [x13]
    add     x13, x13, #64
    st1w    {z23.s}, p0, [x13]

    // Epilogue: restore callee-saved registers
    ldp     d12, d13, [sp, #64]
    ldp     d10, d11, [sp, #48]
    ldp     d8, d9, [sp, #32]
    ldp     x21, x22, [sp, #16]
    ldp     x19, x20, [sp], #80
    ret

    .size tinyshogi_a64fx_sgemm_3x8, .-tinyshogi_a64fx_sgemm_3x8
