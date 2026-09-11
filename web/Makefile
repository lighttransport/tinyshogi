EMCC ?= emcc
BUILD_DIR ?= build
TARGET := $(BUILD_DIR)/tinyshogi.js
EMCC_ENV = $(if $(EM_CACHE),EM_CACHE=$(EM_CACHE),)

# No pthread flags are used by default. The WASM API includes the single-thread
# search backend; the UI invokes it from engine-worker.js.
EMCCFLAGS ?= -O2 -std=c11 -sENVIRONMENT=web -sMODULARIZE=1 -sEXPORT_ES6=1 \
	-sFORCE_FILESYSTEM=1 \
	-sALLOW_MEMORY_GROWTH=1 \
	-sSTACK_SIZE=1048576 \
	-sEXPORTED_RUNTIME_METHODS='["cwrap","FS"]' \
	-sEXPORTED_FUNCTIONS='["_web_init","_web_reset","_web_piece_at","_web_side_to_move","_web_hand_count","_web_legal_move_count","_web_move_from","_web_move_to","_web_move_promotes","_web_move_drop","_web_play_move","_web_play_usi","_web_can_undo","_web_can_redo","_web_history_count","_web_history_move","_web_timeline_count","_web_timeline_move","_web_undo","_web_redo","_web_get_sfen","_web_get_root_sfen","_web_set_sfen","_web_engine_move","_web_engine_last_nodes","_web_engine_last_score","_web_engine_last_depth","_web_engine_last_time_ms","_web_engine_last_nps","_web_game_result","_web_nnue_active","_web_nnue_feature_count","_web_nnue_feature_id","_web_nnue_move_feature_count","_web_nnue_move_feature_id"]'

.PHONY: all clean

all: $(TARGET)

$(TARGET): web_api.c web_thread.c ../examples/yaneuraou_nnue_direct.c ../src/search.c ../src/search.h ../src/eval.c ../src/eval.h ../src/nnue.c ../src/nnue.h ../src/shogi.c ../src/shogi.h ../eval/hao/eval/nn.bin
	@mkdir -p $(BUILD_DIR)
	$(EMCC_ENV) $(EMCC) $(EMCCFLAGS) -I../src -DTINYSHOGI_WEB_NNUE web_api.c web_thread.c ../examples/yaneuraou_nnue_direct.c ../src/search.c ../src/eval.c ../src/nnue.c ../src/simd.c ../src/shogi.c -o $@

clean:
	rm -rf $(BUILD_DIR)
