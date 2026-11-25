# SPDX-License-Identifier: Apache-2.0
CC      ?= gcc
CFLAGS  ?= -std=c11 -O2 -Wall -Wextra -Wpedantic -Werror -Iinclude
LDFLAGS ?= -lm

ifeq ($(OS),Windows_NT)
  EXE := .exe
else
  EXE :=
endif

BUILD_DIR := build

.PHONY: all test sanitizers clean

all: $(BUILD_DIR)/triad_cli$(EXE) $(BUILD_DIR)/test_triad_core$(EXE)

$(BUILD_DIR):
	mkdir -p $(BUILD_DIR)

$(BUILD_DIR)/triad_cli$(EXE): src/triad_core.c src/triad_cli.c include/triad_core.h | $(BUILD_DIR)
	$(CC) $(CFLAGS) src/triad_core.c src/triad_cli.c -o $@ $(LDFLAGS)

$(BUILD_DIR)/test_triad_core$(EXE): src/triad_core.c tests/test_triad_core.c include/triad_core.h | $(BUILD_DIR)
	$(CC) $(CFLAGS) src/triad_core.c tests/test_triad_core.c -o $@ $(LDFLAGS)

test: all
	./$(BUILD_DIR)/test_triad_core$(EXE)

sanitizers: | $(BUILD_DIR)
	$(CC) -std=c11 -O1 -g -Wall -Wextra -Wpedantic -Werror -fsanitize=address,undefined -fno-omit-frame-pointer \
	  -Iinclude src/triad_core.c tests/test_triad_core.c -o $(BUILD_DIR)/test_triad_core_san$(EXE) $(LDFLAGS)
	./$(BUILD_DIR)/test_triad_core_san$(EXE)

clean:
	rm -rf $(BUILD_DIR)
