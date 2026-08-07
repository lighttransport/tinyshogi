#include "../src/a64fx_sdot_gemm.h"
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
enum { M=6, N=32 };
static int64_t ref(const int16_t*a,const int16_t*b,int k,int r,int c){int64_t s=0;for(int i=0;i<k;++i)s+=(int64_t)a[r*k+i]*b[i*N+c];return s;}
int main(int ac,char**av){int K=ac>1?atoi(av[1]):256,R=ac>2?atoi(av[2]):1000;if(K<=0||(K&3))return 2;
 int16_t*a=malloc((size_t)M*K*2),*b=malloc((size_t)K*N*2),*ap=malloc((size_t)K*6*2),*bp=malloc((size_t)K*N*2);int64_t*c=calloc((size_t)M*N,sizeof(*c));if(!a||!b||!ap||!bp||!c)return 1;
 for(int i=0;i<M*K;++i)a[i]=(int16_t)(i%31-15);for(int i=0;i<K*N;++i)b[i]=(int16_t)(i%19-9);
 for(int s=0;s<K/4;++s)for(int r=0;r<M;++r)for(int j=0;j<4;++j)ap[s*24+r*4+j]=a[r*K+s*4+j];
 for(int s=0;s<K/4;++s)for(int v=0;v<4;++v)for(int lane=0;lane<8;++lane)for(int j=0;j<4;++j)bp[s*128+v*32+lane*4+j]=b[(s*4+j)*N+v*8+lane];
 tinyshogi_a64fx_sdot_gemm_6x4_i16(K,ap,bp,c,N);for(int r=0;r<M;++r)for(int col=0;col<N;++col)if(c[r*N+col]!=ref(a,b,K,r,col)){printf("FAIL row=%d col=%d\n",r,col);return 1;}
 memset(c,0,(size_t)M*N*sizeof(*c));for(int i=0;i<R;++i)tinyshogi_a64fx_sdot_gemm_6x4_i16(K,ap,bp,c,N);printf("PASS checksum=%lld rounds=%d\n",(long long)c[0],R);free(a);free(b);free(ap);free(bp);free(c);return 0;}
