#include "../src/a64fx_sgemm.h"
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

enum { MR = 64, NR = 5 };
int main(int argc, char **argv) {
    int K=argc>1?atoi(argv[1]):256, rounds=argc>2?atoi(argv[2]):100;
    float *a=malloc((size_t)K*MR*16*sizeof(*a)),
          *b=malloc((size_t)K*NR*4*sizeof(*b)),
          *c=calloc(MR*NR*16,sizeof(*c));
    if(!a||!b||!c)return 1;
    for(int i=0;i<K*MR*16;i++)a[i]=(float)(i%17)*0.01f;
    for(int i=0;i<K*NR*4;i++)b[i]=(float)(i%13)*0.02f;
    for(int i=0;i<rounds;i++)tinyshogi_a64fx_sgemm_4x5(K,a,b,c,MR);
    printf("%g\n",(double)c[0]); free(a);free(b);free(c);return 0;
}
