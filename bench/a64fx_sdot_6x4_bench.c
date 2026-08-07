#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
extern void tinyshogi_a64fx_sdot_gemm_6x4(int64_t,const int8_t*,const int8_t*,int32_t*,int64_t);
enum { M=6, N=64 };
static int32_t ref(const int8_t*a,const int8_t*b,int k,int r,int c){int32_t s=0;for(int i=0;i<k;++i)s+=(int32_t)a[r*k+i]*b[i* N+c];return s;}
int main(int ac,char**av){int K=ac>1?atoi(av[1]):256,R=ac>2?atoi(av[2]):1000;if(K<=0||(K&3))return 2;
 int8_t*a=malloc((size_t)M*K),*b=malloc((size_t)K*N),*ap=malloc((size_t)K*6),*bp=malloc((size_t)K*N);int32_t*c=calloc((size_t)M*N,sizeof(*c));if(!a||!b||!ap||!bp||!c)return 1;
 for(int i=0;i<M*K;++i)a[i]=(int8_t)(i%127-63);for(int i=0;i<K*N;++i)b[i]=(int8_t)(i%61-30);
 for(int s=0;s<K/4;++s)for(int row=0;row<M;++row)for(int j=0;j<4;++j)ap[s*24+row*4+j]=a[row*K+s*4+j];
 /* B vectors are indexed by K-group and contain four K values per lane. */
 for(int s=0;s<K/4;++s)for(int v=0;v<4;++v)for(int lane=0;lane<16;++lane)for(int j=0;j<4;++j)bp[s*256+v*64+lane*4+j]=b[(s*4+j)*N+v*16+lane];
 tinyshogi_a64fx_sdot_gemm_6x4(K,ap,bp,c,N);for(int row=0;row<M;++row)for(int col=0;col<N;++col)if(c[row*N+col]!=ref(a,b,K,row,col)){printf("FAIL row=%d col=%d got=%d ref=%d\n",row,col,c[row*N+col],ref(a,b,K,row,col));return 1;}
 memset(c,0,(size_t)M*N*sizeof(*c));for(int i=0;i<R;++i)tinyshogi_a64fx_sdot_gemm_6x4(K,ap,bp,c,N);printf("PASS checksum=%d rounds=%d\n",c[0],R);free(a);free(b);free(ap);free(bp);free(c);return 0;}
