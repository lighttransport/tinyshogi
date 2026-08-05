EMCC ?= emcc
BUILD_DIR ?= build
TARGET := $(BUILD_DIR)/tinyshogi.js
EMCC_ENV = $(if $(EM_CACHE),EM_CACHE=$(EM_CACHE),)

# No pthread flags are used by default. The web API intentionally links only
# the rules engine, so the browser build stays small and single-threaded.
EMCCFLAGS ?= -O2 -std=c11 -sENVIRONMENT=web -sMODULARIZE=1 -sEXPORT_ES6=1 \
	-sALLOW_MEMORY_GROWTH=1 \
	-sEXPORTED_RUNTIME_METHODS='["cwrap"]' \
	-sEXPORTED_FUNCTIONS='["_web_init","_web_reset","_web_piece_at","_web_side_to_move","_web_hand_count","_web_legal_move_count","_web_move_from","_web_move_to","_web_move_promotes","_web_move_drop","_web_play_move","_web_game_result"]'

.PHONY: all clean

all: $(TARGET)

$(TARGET): web_api.c ../src/shogi.c ../src/shogi.h
	@mkdir -p $(BUILD_DIR)
	$(EMCC_ENV) $(EMCC) $(EMCCFLAGS) web_api.c ../src/shogi.c -o $@

clean:
	rm -rf $(BUILD_DIR)
