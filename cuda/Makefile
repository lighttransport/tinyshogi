CC ?= cc
CUEW_DIR ?= ../third_party/cuew
BUILD ?= build

CFLAGS ?= -O2 -g -Wall -Wextra -Wpedantic -std=c11

.PHONY: all probe feature-encode train-linear clean

all: probe

$(BUILD):
	mkdir -p $(BUILD)

$(BUILD)/cuew.o: $(CUEW_DIR)/cuew.c $(CUEW_DIR)/cuew.h | $(BUILD)
	$(CC) -I$(CUEW_DIR) -O2 -g -w -c $< -o $@

$(BUILD)/cuew_probe.o: cuew_probe.c $(CUEW_DIR)/cuew.h | $(BUILD)
	$(CC) $(CFLAGS) -I$(CUEW_DIR) -c $< -o $@

probe: $(BUILD)/cuew.o $(BUILD)/cuew_probe.o
	$(CC) $(CFLAGS) $^ -ldl -o $(BUILD)/tinyshogi-cuda-probe

$(BUILD)/feature_encode.o: feature_encode.c $(CUEW_DIR)/cuew.h | $(BUILD)
	$(CC) $(CFLAGS) -I$(CUEW_DIR) -c $< -o $@

feature-encode: $(BUILD)/cuew.o $(BUILD)/feature_encode.o
	$(CC) $(CFLAGS) $^ -ldl -o $(BUILD)/tinyshogi-feature-encode

$(BUILD)/train_linear.o: train_linear.c $(CUEW_DIR)/cuew.h | $(BUILD)
	$(CC) $(CFLAGS) -I$(CUEW_DIR) -c $< -o $@

train-linear: $(BUILD)/cuew.o $(BUILD)/train_linear.o
	$(CC) $(CFLAGS) $^ -ldl -o $(BUILD)/tinyshogi-train-linear

clean:
	rm -rf $(BUILD)
