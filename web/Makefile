EMCC ?= emcc
BUILD_DIR ?= build
TARGET := $(BUILD_DIR)/tinyshogi.js
EMCC_ENV = $(if $(EM_CACHE),EM_CACHE=$(EM_CACHE),)

# No pthread flags are used by default. The WASM API includes the single-thread
# search backend; the UI invokes it from engine-worker.js.
EMCCFLAGS ?= -O2 -std=c11 -sENVIRONMENT=web -sMODULARIZE=1 -sEXPORT_ES6=1 \
	-sALLOW_MEMORY_GROWTH=1 \
	-sEXPORTED_RUNTIME_METHODS='["cwrap"]' \
	-sEXPORTED_FUNCTIONS='["_web_init","_web_reset","_web_piece_at","_web_side_to_move","_web_hand_count","_web_legal_move_count","_web_move_from","_web_move_to","_web_move_promotes","_web_move_drop","_web_play_move","_web_play_usi","_web_can_undo","_web_can_redo","_web_undo","_web_redo","_web_get_sfen","_web_set_sfen","_web_engine_move","_web_game_result"]'

.PHONY: all clean

all: $(TARGET)

$(TARGET): web_api.c web_thread.c ../src/search.c ../src/search.h ../src/eval.c ../src/eval.h ../src/shogi.c ../src/shogi.h
	@mkdir -p $(BUILD_DIR)
	$(EMCC_ENV) $(EMCC) $(EMCCFLAGS) web_api.c web_thread.c ../src/search.c ../src/eval.c ../src/shogi.c -o $@

clean:
	rm -rf $(BUILD_DIR)
