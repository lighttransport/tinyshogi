CC ?= cc
BUILD ?= build
CFLAGS ?= -O2 -g -Wall -Wextra -Wpedantic -std=c11

.PHONY: all probe clean

all: probe

$(BUILD):
	mkdir -p $(BUILD)

$(BUILD)/rocew.o: rocew.c rocew.h | $(BUILD)
	$(CC) $(CFLAGS) -c $< -o $@

$(BUILD)/probe.o: probe.c rocew.h | $(BUILD)
	$(CC) $(CFLAGS) -c $< -o $@

probe: $(BUILD)/rocew.o $(BUILD)/probe.o
	$(CC) $(CFLAGS) $^ -ldl -o $(BUILD)/tinyshogi-rocm-probe

clean:
	rm -rf $(BUILD)
