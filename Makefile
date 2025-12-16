KNOWNTARGETS := CoqMakefile all src examples libraries clean cleanall \
                count deps doc help status verify
KNOWNFILES   := Makefile _CoqProject

.DEFAULT_GOAL := src

# Generate CoqMakefile from _CoqProject
CoqMakefile: Makefile _CoqProject
	$(COQBIN)coq_makefile -f _CoqProject -o CoqMakefile

# Invoke the generated makefile for standard targets
invoke-coqmakefile: CoqMakefile
	$(MAKE) --no-print-directory -f CoqMakefile $(filter-out $(KNOWNTARGETS),$(MAKECMDGOALS))

.PHONY: invoke-coqmakefile $(KNOWNFILES)

# Configuration

COQ_OPTS := -R src QWIRE -R libraries QWIRE.Libraries -R examples QWIRE.Examples

# Directories
SRC_DIR    := src
EX_DIR     := examples
LIB_DIR    := libraries
BASE_DIR   := $(SRC_DIR)/Base
SYNTAX_DIR := $(SRC_DIR)/Syntax
TYPING_DIR := $(SRC_DIR)/Typing
SEM_DIR    := $(SRC_DIR)/Semantics
COMP_DIR   := $(SRC_DIR)/CompilationQASM
ALG_DIR    := $(LIB_DIR)/algorithms
DOC_DIR    := docs

# Main Targets

.PHONY: all src examples libraries clean cleanall cleanuser

# Default: build everything in src/ 
src:
	@echo "Building core QWIRE framework (src/)..."
	@$(MAKE) CoqMakefile > /dev/null 2>&1 || true
	@$(MAKE) --no-print-directory -f CoqMakefile \
		$(SRC_DIR)/Base/Contexts.vo \
		$(SRC_DIR)/Base/Monad.vo \
		$(SRC_DIR)/Base/Monoid.vo \
		$(SRC_DIR)/Syntax/HOAS/HOASCircuits.vo \
		$(SRC_DIR)/Syntax/HOAS/HOASLib.vo \
		$(SRC_DIR)/Syntax/DB/DBCircuits.vo \
		$(SRC_DIR)/Typing/TypeChecking.vo \
		$(SRC_DIR)/Semantics/Denotation.vo \
		$(SRC_DIR)/Semantics/SemanticLib.vo \
		$(SRC_DIR)/Semantics/Composition.vo \
		$(SRC_DIR)/Semantics/UnitarySemantics.vo \
		$(SRC_DIR)/Semantics/Oracles.vo \
		$(SRC_DIR)/Semantics/Ancilla.vo \
		$(SRC_DIR)/Semantics/Symmetric.vo \
		$(SRC_DIR)/CompilationQASM/QASM.vo \
		$(SRC_DIR)/CompilationQASM/QASMPrinter.vo
	@echo "✓ Core QWIRE framework complete!"

# Build all libraries
libraries: src
	@echo "Building libraries..."
	@$(MAKE) --no-print-directory -f CoqMakefile \
		$(LIB_DIR)/Equations.vo \
		$(ALG_DIR)/Arithmetic.vo \
		$(ALG_DIR)/Deutsch.vo \
		$(ALG_DIR)/GHZ.vo
	@echo "✓ Libraries complete!"

# Build all examples
examples: libraries
	@echo "Building examples..."
	@$(MAKE) --no-print-directory -f CoqMakefile \
		$(EX_DIR)/HOASExamples.vo \
		$(EX_DIR)/HOASProofs.vo \
		$(EX_DIR)/QASMExamples.vo
	@echo "✓ Examples complete!"

# Build everything
all: src libraries examples
	@echo "✓ Complete QWIRE build finished!"

# User file compilation: make <filename>.vo
# This builds a user .v file in the root directory along with necessary dependencies
%.vo: %.v src libraries
	@echo "Building user file: $<"
	coqc $(COQ_OPTS) $<
	@echo "✓ User file $< compiled successfully!"

# Cleaning Targets

clean: CoqMakefile
	@echo "Cleaning generated files..."
	$(MAKE) -f CoqMakefile clean
	@find . -name "*.vo" -o -name "*.vok" -o -name "*.vos" \
	     -o -name "*.glob" -o -name "*.aux" -o -name ".*.aux" \
	     -o -name "*.timing" | xargs rm -f
	@echo "✓ Clean complete"

cleanall: clean
	@echo "Cleaning documentation and CoqMakefile..."
	@rm -rf $(DOC_DIR)
	@rm -f CoqMakefile CoqMakefile.conf
	@echo "✓ Deep clean complete"

# Clean only user files (in root directory)
cleanuser:
	@echo "Cleaning user files in root directory..."
	@find . -maxdepth 1 -name "*.vo" -o -name "*.vok" -o -name "*.vos" \
	     -o -name "*.glob" -o -name "*.aux" -o -name ".*.aux" \
	     -o -name "*.timing" | xargs rm -f 2>/dev/null || true
	@echo "✓ User files cleaned (src/, libraries/, examples/ preserved)"

# Help target
help:
	@echo "QWIRE Build System"
	@echo "=================="
	@echo ""
	@echo "Main targets:"
	@echo "  make             - Build all files in src/ (default)"
	@echo "  make src         - Build all files in src/"
	@echo "  make libraries   - Build all library files"
	@echo "  make examples    - Build all example files"
	@echo "  make all         - Build everything (src + libraries + examples)"
	@echo ""
	@echo "User files:"
	@echo "  make myfile.vo   - Compile myfile.v in root directory"
	@echo "                     (automatically builds src/ and libraries/ first)"
	@echo ""
	@echo "Cleaning:"
	@echo "  make clean       - Remove all compiled files"
	@echo "  make cleanuser   - Remove only user files (preserve src/libraries/examples/)"
	@echo "  make cleanall    - Deep clean (including CoqMakefile)"
	@echo ""