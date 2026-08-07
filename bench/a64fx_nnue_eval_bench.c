#include "../src/nnue.h"
#include <stdio.h>
#include <stdlib.h>
int main(int ac,char**av){int rounds=ac>1?atoi(av[1]):1000;shogi_init();ShogiNnueModel m;shogi_nnue_model_init(&m);if(!shogi_nnue_model_init_default(&m,256))return 1;for(size_t i=0;i<(size_t)m.feature_count*m.hidden_dim;++i)m.feature_weights[i]=(int16_t)(i%17-8);for(size_t i=0;i<(size_t)m.hidden_dim*2;++i)m.output_weights[i]=(int16_t)(i%13-6);ShogiPosition p;shogi_position_start(&p);long long s=0;for(int i=0;i<rounds;++i)s+=shogi_nnue_evaluate_position(&m,&p,SHOGI_BLACK);printf("PASS sum=%lld rounds=%d\n",s,rounds);shogi_nnue_model_destroy(&m);return 0;}
