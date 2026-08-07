CC ?= cc
CUDA_CXX ?= nvcc
HIP_CXX ?= hipcc
BUILD ?= build
CFLAGS ?= -O2 -g -Wall -Wextra -Wpedantic -std=c11

.PHONY: cuda rocm clean

$(BUILD):
	mkdir -p $(BUILD)

$(BUILD)/nnue.o: ../src/nnue.c ../src/nnue.h ../src/shogi.h | $(BUILD)
	$(CC) $(CFLAGS) -I../src -c $< -o $@

$(BUILD)/shogi.o: ../src/shogi.c ../src/shogi.h | $(BUILD)
	$(CC) $(CFLAGS) -I../src -c $< -o $@

cuda: $(BUILD)/nnue.o $(BUILD)/shogi.o
	$(CUDA_CXX) -O3 -std=c++14 -I../src train_nnue.cu $(BUILD)/nnue.o $(BUILD)/shogi.o -o $(BUILD)/tinyshogi-train-nnue-cuda

rocm: $(BUILD)/nnue.o $(BUILD)/shogi.o
	$(HIP_CXX) -O3 -std=c++14 -I../src train_nnue.cu $(BUILD)/nnue.o $(BUILD)/shogi.o -o $(BUILD)/tinyshogi-train-nnue-hip

clean:
	rm -rf $(BUILD)
