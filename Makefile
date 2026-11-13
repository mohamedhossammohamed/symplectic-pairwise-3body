# Makefile for MHMZAHRAN/symplectic-pairwise-3body
# Zero-dependency C99 reference solver + strict CI unit-test suite + Lean 4 + LaTeX

CC        ?= cc
CFLAGS    := -std=c99 -O3 -Wall -Wextra -Werror -pedantic -fno-fast-math
LDFLAGS   := -lm

BIN_DIR   := build
TARGET    := $(BIN_DIR)/symplectic_3body
TEST_BIN  := $(BIN_DIR)/test_invariants

C_SRC     := src/mhmzahran_symplectic_3body.c
TEST_SRC  := tests/test_invariants.c

.PHONY: all c test-c verify-lean paper clean check

all: c $(TEST_BIN) verify-lean

$(BIN_DIR):
	mkdir -p $(BIN_DIR)

c: $(TARGET) $(TEST_BIN)

$(TARGET): $(C_SRC) | $(BIN_DIR)
	$(CC) $(CFLAGS) $(C_SRC) -o $(TARGET) $(LDFLAGS)

$(TEST_BIN): $(TEST_SRC) | $(BIN_DIR)
	$(CC) $(CFLAGS) $(TEST_SRC) -o $(TEST_BIN) $(LDFLAGS)

test-c: $(TARGET) $(TEST_BIN)
	@echo "Running C99 Symplectic Pairwise 3-Body benchmark..."
	./$(TARGET)
	@echo ""
	@echo "Running strict C99 CI assertion suite (tolerance <= 1e-13)..."
	./$(TEST_BIN)

verify-lean:
	@echo "Fetching Mathlib4 cache and verifying Lean 4 proofs..."
	lake exe cache get
	lake build SymplecticThreeBody

paper:
	@echo "Compiling standalone LaTeX manuscript..."
	cd paper && pdflatex -interaction=nonstopmode main.tex && pdflatex -interaction=nonstopmode main.tex

check: test-c verify-lean
	@echo "All C99 strict invariant assertions and Lean 4 formal proofs passed."

clean:
	rm -rf $(BIN_DIR) paper/*.aux paper/*.log paper/*.out paper/*.pdf
