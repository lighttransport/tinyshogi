CC ?= cc
CFLAGS ?= -O3 -g -Wall -Wextra -Wpedantic -std=c11
.PHONY: train-int eval-int train-nnue eval-nnue brute-server clean
train-int: train_int
eval-int: eval_int
train-nnue: train_nnue
eval-nnue: eval_nnue
brute-server: brute_server
train_int: train_int.c ../src/int_math.c ../src/simd.c ../src/int_math.h
	$(CC) $(CFLAGS) train_int.c ../src/int_math.c ../src/simd.c -o $@
eval_int: eval_int.c ../src/int_math.c ../src/int_model.c ../src/simd.c ../src/int_math.h ../src/int_model.h
	$(CC) $(CFLAGS) eval_int.c ../src/int_math.c ../src/int_model.c ../src/simd.c -o $@
train_nnue: train_nnue.c ../src/nnue.c ../src/simd.c ../src/nnue.h ../src/shogi.c ../src/shogi.h
	$(CC) $(CFLAGS) train_nnue.c ../src/nnue.c ../src/simd.c ../src/shogi.c -lm -o $@
eval_nnue: eval_nnue.c ../src/nnue.c ../src/simd.c ../src/nnue.h ../src/shogi.c ../src/shogi.h
	$(CC) $(CFLAGS) eval_nnue.c ../src/nnue.c ../src/simd.c ../src/shogi.c -lm -o $@
brute_server: ../tools/bruteforce_server.c ../src/brute.c ../src/brute.h ../src/shogi.c ../src/shogi.h
	$(CC) $(CFLAGS) -I../src ../tools/bruteforce_server.c ../src/brute.c ../src/shogi.c -o $@
clean:
	rm -f train_int eval_int train_nnue eval_nnue brute_server
