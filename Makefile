CC ?= cc
.DEFAULT_GOAL := all
PYTHON ?= python3
BUILD ?= build/make
DL ?= 0
HIPBLASLT ?= 0
ROCM_PATH ?= /opt/rocm/core
HIPBLASLT_INCLUDE ?= $(ROCM_PATH)/include
HIPBLASLT_LIB ?= $(ROCM_PATH)/lib
GEMM_DIR ?= third_party/gemm

CPPFLAGS ?= -Isrc
CFLAGS ?= -O2 -g -Wall -Wextra -Wpedantic -std=c11
LDLIBS ?= -pthread -lm -ldl

ifeq ($(DL),1)
CPPFLAGS += -DTINYSHOGI_DL -I$(GEMM_DIR)/nn
DL_OBJECTS := $(BUILD)/src/dl_eval.o $(BUILD)/src/dl_features.o $(BUILD)/gn.o $(BUILD)/gn_cpu.o $(BUILD)/gn_gpu.o $(BUILD)/cuew.o $(BUILD)/rocew.o
ifeq ($(HIPBLASLT),1)
DL_OBJECTS := $(filter-out $(BUILD)/gn_gpu.o,$(DL_OBJECTS)) $(BUILD)/gn_gpu_lt.o $(BUILD)/gn_hipblaslt.o
LDLIBS += -L$(HIPBLASLT_LIB) -Wl,-rpath,$(HIPBLASLT_LIB) -lhipblaslt -lamdhip64 -lstdc++
endif
endif

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
.PHONY: dl dl-check
dl:
	$(MAKE) DL=1 BUILD=build/dl all build/dl/dl-selfplay build/dl/dl-test
	$(MAKE) -C $(GEMM_DIR)/nn all
dl-check: dl
	build/dl/dl-test
	$(MAKE) -C $(GEMM_DIR)/nn check
	$(PYTHON) -B tests/test_dl_pipeline.py
	$(PYTHON) -B tests/test_dl_tools.py

$(BUILD)/gn.o: $(GEMM_DIR)/nn/gn.c $(GEMM_DIR)/nn/gn.h $(GEMM_DIR)/nn/gn_internal.h $(GEMM_DIR)/nn/gn_cpu.h $(GEMM_DIR)/common/safetensors.h $(GEMM_DIR)/common/safetensors_writer.h | $(BUILD)
	$(CC) $(CPPFLAGS) $(CFLAGS) -c $< -o $@
$(BUILD)/gn_kernels.inc: $(GEMM_DIR)/nn/gn_kernels.cu $(GEMM_DIR)/nn/gn_sm120.cuh $(GEMM_DIR)/nn/gn_rdna4.cuh $(GEMM_DIR)/nn/embed_kernels.py | $(BUILD)
	$(PYTHON) -B $(GEMM_DIR)/nn/embed_kernels.py $< $@
.PHONY: dl-build-config-force
dl-build-config-force:
$(BUILD)/dl-backend.config: dl-build-config-force | $(BUILD)
	@$(PYTHON) -B $(GEMM_DIR)/nn/build_config.py $@ '$(HIPBLASLT)' '$(HIPBLASLT_INCLUDE)' '$(HIPBLASLT_LIB)'
$(BUILD)/gn_gpu.o: $(GEMM_DIR)/nn/gn_gpu.c $(GEMM_DIR)/nn/gn_internal.h $(GEMM_DIR)/nn/gn.h $(BUILD)/gn_kernels.inc $(BUILD)/dl-backend.config
	$(CC) $(CPPFLAGS) $(CFLAGS) -Wno-overlength-strings -I$(BUILD) -c $< -o $@
$(BUILD)/gn_gpu_lt.o: $(GEMM_DIR)/nn/gn_gpu.c $(GEMM_DIR)/nn/gn_internal.h $(GEMM_DIR)/nn/gn.h $(GEMM_DIR)/nn/gn_hipblaslt.h $(BUILD)/gn_kernels.inc $(BUILD)/dl-backend.config
	$(CC) $(CPPFLAGS) $(CFLAGS) -DGN_HIPBLASLT=1 -Wno-overlength-strings -I$(BUILD) -c $< -o $@
$(BUILD)/gn_hipblaslt.o: $(GEMM_DIR)/nn/gn_hipblaslt.cpp $(GEMM_DIR)/nn/gn_hipblaslt.h $(BUILD)/dl-backend.config | $(BUILD)
	$(CXX) -O2 -std=c++17 -Wall -Wextra -D__HIP_PLATFORM_AMD__ -I$(ROCM_PATH)/include -I$(HIPBLASLT_INCLUDE) -c $< -o $@
$(BUILD)/gn_cpu.o: $(GEMM_DIR)/nn/gn_cpu.c $(GEMM_DIR)/nn/gn_cpu.h $(GEMM_DIR)/nn/gn_internal.h $(GEMM_DIR)/nn/gn.h | $(BUILD)
	$(CC) $(CPPFLAGS) $(CFLAGS) -c $< -o $@
$(BUILD)/cuew.o: $(GEMM_DIR)/cuda/cuew.c Makefile | $(BUILD)
	$(CC) -O2 -fvisibility=hidden -c $< -o $@
$(BUILD)/rocew.o: $(GEMM_DIR)/rdna4/rocew.c Makefile | $(BUILD)
	$(CC) -O2 -fvisibility=hidden -c $< -o $@

$(BUILD)/dl-selfplay: tools/dl_selfplay.c $(GEMM_DIR)/nn/gn_replay.h $(DL_OBJECTS) $(BUILD)/src/search.o $(BUILD)/src/shogi.o $(BUILD)/src/eval.o $(BUILD)/src/thread_posix.o
	$(CC) $(CPPFLAGS) $(CFLAGS) $(filter %.c %.o,$^) $(LDLIBS) -o $@

$(BUILD)/dl-test: tests/test_dl.c $(DL_OBJECTS) $(BUILD)/src/search.o $(BUILD)/src/shogi.o $(BUILD)/src/eval.o $(BUILD)/src/thread_posix.o
	$(CC) $(CPPFLAGS) $(CFLAGS) $^ $(LDLIBS) -o $@

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
	$(BUILD)/src/thread_posix.o $(DL_OBJECTS) | $(BUILD)
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
