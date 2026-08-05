CC := clang
TARGET := shogi-fuzz
FUZZ_FLAGS ?= -fsanitize=fuzzer,address,undefined -fno-omit-frame-pointer -O1 -g

.PHONY: all run clean

all: $(TARGET)

$(TARGET): shogi_fuzz.c ../src/shogi.c ../src/shogi.h
	$(CC) $(FUZZ_FLAGS) -std=c11 -I../src shogi_fuzz.c ../src/shogi.c -o $@

run: $(TARGET)
	./$(TARGET) -max_len=1024 corpus

clean:
	rm -f $(TARGET)
