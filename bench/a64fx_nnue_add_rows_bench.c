#include "../src/simd.h"
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int main(int ac,char**av){enum{N=256,R=54};int rounds=ac>1?atoi(av[1]):1000;int row_count=ac>2?atoi(av[2]):R;int32_t a[N],ref[N];int16_t w[R][N];const int16_t*rows[R];for(int r=0;r<R;++r)rows[r]=w[r];for(int i=0;i<N;++i){a[i]=i-128;ref[i]=a[i];for(int r=0;r<row_count;++r){w[r][i]=(int16_t)(r*17+i%11-5);ref[i]+=w[r][i];}}tinyshogi_add_i16_i32_rows(a,rows,row_count,N,1);for(int i=0;i<N;++i)if(a[i]!=ref[i]){printf("FAIL rows=%d i=%d got=%d ref=%d w=%d\n",row_count,i,a[i],ref[i],w[0][i]);for(int j=0;j<12;++j)printf(" %d:%d/%d",j,a[j],ref[j]);putchar('\n');return 1;}for(int i=1;i<rounds;++i)tinyshogi_add_i16_i32_rows(a,rows,row_count,N,1);printf("PASS %d rounds=%d rows=%d\n",a[0],rounds,row_count);return 0;}
