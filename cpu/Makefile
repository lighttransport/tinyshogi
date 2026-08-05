CC ?= cc
CFLAGS ?= -O3 -g -Wall -Wextra -Wpedantic -std=c11
.PHONY: train-int eval-int clean
train-int: train_int
eval-int: eval_int
train_int: train_int.c ../src/int_math.c ../src/int_math.h
	$(CC) $(CFLAGS) train_int.c ../src/int_math.c -o $@
eval_int: eval_int.c ../src/int_math.c ../src/int_model.c ../src/int_math.h ../src/int_model.h
	$(CC) $(CFLAGS) eval_int.c ../src/int_math.c ../src/int_model.c -o $@
clean:
	rm -f train_int eval_int
