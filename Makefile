CC ?= cc
PYTHON ?= python3
BUILD ?= build/make

CPPFLAGS ?= -Isrc
CFLAGS ?= -O2 -g -Wall -Wextra -Wpedantic -std=c11
LDLIBS ?= -pthread -lm -ldl

ENGINE := $(BUILD)/tinyshogi
TESTS := \
	$(BUILD)/tinyshogi-rules-test \
	$(BUILD)/tinyshogi-search-test \
	$(BUILD)/tinyshogi-search-hash-test \
	$(BUILD)/tinyshogi-nnue-test \
	$(BUILD)/tinyshogi-brute-test \
	$(BUILD)/tinyshogi-integer-test \
	$(BUILD)/tinyshogi-integer-batch-test \
	$(BUILD)/tinyshogi-simd-test \
	$(BUILD)/tinyshogi-yaneuraou-nnue-test
BENCHMARKS := \
	$(BUILD)/tinyshogi-simd-bench \
	$(BUILD)/tinyshogi-nnue-state-bench \
	$(BUILD)/tinyshogi-nnue-batch-bench \
	$(BUILD)/tinyshogi-perpetual-bench

.PHONY: all test check benchmarks examples clean

all: $(ENGINE) $(TESTS) $(BENCHMARKS) examples

test: $(ENGINE) $(TESTS)
	$(ENGINE) --selftest
	$(BUILD)/tinyshogi-rules-test
	$(BUILD)/tinyshogi-search-test
	$(BUILD)/tinyshogi-search-hash-test
	$(BUILD)/tinyshogi-nnue-test
	$(BUILD)/tinyshogi-brute-test
	$(BUILD)/tinyshogi-integer-test
	$(BUILD)/tinyshogi-integer-batch-test
	$(BUILD)/tinyshogi-simd-test
	$(PYTHON) -B tests/test_match_tools.py $(ENGINE)
	$(PYTHON) -B tests/test_mcp.py $(ENGINE)
	if [ -r "$${YANEURAOU_NN_BIN:-eval/nn.bin}" ]; then \
		YANEURAOU_NN_BIN="$${YANEURAOU_NN_BIN:-eval/nn.bin}" $(BUILD)/tinyshogi-yaneuraou-nnue-test; \
	fi

check: test

benchmarks: $(BENCHMARKS)

examples: $(BUILD)/tinyshogi-eval-plugin.so \
	$(BUILD)/tinyshogi-yaneuraou-nnue-direct.so \
	$(BUILD)/tinyshogi-yaneuraou-eval-adapter.so

$(BUILD):
	mkdir -p $@

$(BUILD)/src/%.o: src/%.c
	mkdir -p $(@D)
	$(CC) $(CPPFLAGS) $(CFLAGS) -MMD -MP -c $< -o $@

$(BUILD)/tests/%.o: tests/%.c
	mkdir -p $(@D)
	$(CC) $(CPPFLAGS) $(CFLAGS) -MMD -MP -c $< -o $@

$(BUILD)/bench/%.o: bench/%.c
	mkdir -p $(@D)
	$(CC) $(CPPFLAGS) $(CFLAGS) -MMD -MP -c $< -o $@

$(ENGINE): $(BUILD)/src/main.o $(BUILD)/src/search.o $(BUILD)/src/shogi.o \
	$(BUILD)/src/nnue.o $(BUILD)/src/simd.o $(BUILD)/src/eval.o \
	$(BUILD)/src/thread_posix.o | $(BUILD)
	$(CC) $(CFLAGS) $^ $(LDLIBS) -rdynamic -o $@

$(BUILD)/tinyshogi-rules-test: $(BUILD)/tests/test_rules.o $(BUILD)/src/shogi.o | $(BUILD)
	$(CC) $(CFLAGS) $^ $(LDLIBS) -o $@

$(BUILD)/tinyshogi-search-test: $(BUILD)/tests/test_search.o $(BUILD)/src/search.o \
	$(BUILD)/src/shogi.o $(BUILD)/src/eval.o $(BUILD)/src/thread_posix.o | $(BUILD)
	$(CC) $(CFLAGS) $^ $(LDLIBS) -o $@

$(BUILD)/tinyshogi-nnue-test: $(BUILD)/tests/test_nnue.o $(BUILD)/src/nnue.o \
	$(BUILD)/src/simd.o $(BUILD)/src/shogi.o | $(BUILD)
	$(CC) $(CFLAGS) $^ $(LDLIBS) -o $@

$(BUILD)/tinyshogi-search-hash-test: $(BUILD)/tests/test_search_hash.o $(BUILD)/src/shogi.o \
	$(BUILD)/src/eval.o $(BUILD)/src/thread_posix.o | $(BUILD)
	$(CC) $(CFLAGS) $^ $(LDLIBS) -o $@

$(BUILD)/tinyshogi-brute-test: $(BUILD)/tests/test_brute.o $(BUILD)/src/brute.o \
	$(BUILD)/src/shogi.o | $(BUILD)
	$(CC) $(CFLAGS) $^ $(LDLIBS) -o $@

$(BUILD)/tinyshogi-integer-test: $(BUILD)/tests/test_int.o $(BUILD)/src/int_math.o \
	$(BUILD)/src/int_model.o $(BUILD)/src/simd.o | $(BUILD)
	$(CC) $(CFLAGS) $^ $(LDLIBS) -o $@

$(BUILD)/tinyshogi-integer-batch-test: $(BUILD)/tests/test_int_batch.o $(BUILD)/src/int_math.o \
	$(BUILD)/src/int_model.o $(BUILD)/src/simd.o | $(BUILD)
	$(CC) $(CFLAGS) $^ $(LDLIBS) -o $@

$(BUILD)/tinyshogi-simd-test: $(BUILD)/tests/test_simd.o $(BUILD)/src/simd.o | $(BUILD)
	$(CC) $(CFLAGS) $^ $(LDLIBS) -o $@

$(BUILD)/tinyshogi-yaneuraou-nnue-test: $(BUILD)/tests/test_yaneuraou_nnue.o \
		$(BUILD)/examples/yaneuraou_nnue_direct.o $(BUILD)/src/shogi.o \
		$(BUILD)/src/eval.o | $(BUILD)
	$(CC) $(CFLAGS) $^ $(LDLIBS) -rdynamic -o $@

$(BUILD)/tests/test_yaneuraou_nnue.o: tests/test_yaneuraou_nnue.c
	mkdir -p $(@D)
	$(CC) $(CPPFLAGS) $(CFLAGS) -MMD -MP -c $< -o $@

$(BUILD)/examples/yaneuraou_nnue_direct.o: examples/yaneuraou_nnue_direct.c
	mkdir -p $(@D)
	$(CC) $(CPPFLAGS) $(CFLAGS) -MMD -MP -c $< -o $@

$(BUILD)/tinyshogi-simd-bench: $(BUILD)/bench/simd_bench.o $(BUILD)/src/simd.o | $(BUILD)
	$(CC) $(CFLAGS) $^ $(LDLIBS) -o $@

$(BUILD)/tinyshogi-nnue-state-bench: $(BUILD)/bench/nnue_state_bench.o \
	$(BUILD)/src/nnue.o $(BUILD)/src/simd.o $(BUILD)/src/shogi.o | $(BUILD)
	$(CC) $(CFLAGS) $^ $(LDLIBS) -o $@

$(BUILD)/tinyshogi-nnue-batch-bench: $(BUILD)/bench/nnue_batch_bench.o \
	$(BUILD)/src/nnue.o $(BUILD)/src/simd.o $(BUILD)/src/shogi.o | $(BUILD)
	$(CC) $(CFLAGS) $^ $(LDLIBS) -o $@

$(BUILD)/tinyshogi-perpetual-bench: $(BUILD)/bench/perpetual_check_bench.o \
	$(BUILD)/src/search.o $(BUILD)/src/shogi.o $(BUILD)/src/nnue.o \
	$(BUILD)/src/simd.o $(BUILD)/src/eval.o $(BUILD)/src/thread_posix.o | $(BUILD)
	$(CC) $(CFLAGS) $^ $(LDLIBS) -o $@

$(BUILD)/tinyshogi-eval-plugin.so: examples/tinyshogi_eval_plugin.c | $(BUILD)
	$(CC) $(CPPFLAGS) $(CFLAGS) -shared -fPIC $< -o $@

$(BUILD)/tinyshogi-yaneuraou-nnue-direct.so: examples/yaneuraou_nnue_direct.c src/eval.h src/shogi.h | $(BUILD)
	$(CC) $(CPPFLAGS) $(CFLAGS) -shared -fPIC $< -o $@

$(BUILD)/tinyshogi-yaneuraou-eval-adapter.so: examples/yaneuraou_eval_adapter.c | $(BUILD)
	$(CC) $(CPPFLAGS) $(CFLAGS) -shared -fPIC $< $(LDLIBS) -o $@

clean:
	rm -rf $(BUILD)

-include $(wildcard $(BUILD)/src/*.d $(BUILD)/tests/*.d $(BUILD)/bench/*.d $(BUILD)/examples/*.d)
