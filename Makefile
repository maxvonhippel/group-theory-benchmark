# Makefile for gap-agent

# Include sub-makefiles
include make/ai.mk
include make/docs.mk
include make/tests.mk
include make/watch.mk
.PHONY: setup update-gap clean install help extract-test extract-all problems problems-test clean-problems

# Complete project setup
setup:
	@echo "=== Setting up GAP Agent Project ==="
	@echo "Step 1: Initializing git submodule (full clone)..."
	git submodule update --init --recursive
	@echo ""
	@echo "Step 2: Installing Python dependencies (including lean-lsp-mcp)..."
	uv sync
	@echo ""
	@echo "Step 2a: Setting up Lean 4 environment..."
	@if ! command -v brew >/dev/null 2>&1; then \
		echo "Warning: Homebrew not found. Lean setup requires elan (install manually or via homebrew)"; \
	elif ! command -v elan >/dev/null 2>&1; then \
		echo "Installing elan via Homebrew..."; \
		brew install elan-init; \
	else \
		echo "Elan already installed"; \
	fi
	@if command -v elan >/dev/null 2>&1; then \
		echo "Setting default Lean version..."; \
		elan default leanprover/lean4:stable || true; \
		echo "Creating Lean scratch project..."; \
		mkdir -p lean_scratch && cd lean_scratch && lake init LeanScratch 2>/dev/null || echo "Lean scratch project already exists"; \
	fi
	@echo ""
	@echo "Step 3: Checking for GAP build dependencies..."
	@if ! command -v brew >/dev/null 2>&1; then \
		echo "Warning: Homebrew not found. You may need to install gmp and readline manually."; \
	else \
		echo "Installing dependencies via Homebrew (gmp, readline)..."; \
		brew install gmp readline || true; \
	fi
	@echo ""
	@echo "Step 4: Generating configure script..."
	cd gap && ./autogen.sh
	@echo ""
	@echo "Step 5: Configuring GAP..."
	cd gap && ./configure
	@echo ""
	@echo "Step 6: Building GAP..."
	cd gap && $(MAKE)
	@echo ""
	@echo "Step 7: Downloading essential GAP packages..."
	@mkdir -p gap/pkg
	cd gap/pkg && \
		curl -L -o GAPDoc.tar.gz http://www.math.rwth-aachen.de/~Frank.Luebeck/GAPDoc/GAPDoc-1.6.7.tar.gz && \
		tar xzf GAPDoc.tar.gz && rm GAPDoc.tar.gz && \
		curl -L -o SmallGrp.tar.gz https://github.com/gap-packages/SmallGrp/releases/download/v1.5.4/SmallGrp-1.5.4.tar.gz && \
		tar xzf SmallGrp.tar.gz && rm SmallGrp.tar.gz && \
		curl -L -o primgrp.tar.gz https://github.com/gap-packages/primgrp/releases/download/v3.4.4/primgrp-3.4.4.tar.gz && \
		tar xzf primgrp.tar.gz && rm primgrp.tar.gz && \
		curl -L -o transgrp.tar.gz https://www.math.colostate.edu/~hulpke/transgrp/transgrp3.6.5.tar.gz && \
		tar xzf transgrp.tar.gz && rm transgrp.tar.gz
	@echo "Packages: GAPDoc, SmallGrp, primgrp, transgrp installed"
	@echo ""
	@echo "Step 8: Building GAP packages..."
	cd gap && ./bin/BuildPackages.sh --with-gaproot=$$(pwd) --strict || echo "Note: Some optional packages may have failed"
	@echo ""
	@echo "Step 9: Installing AI CLI tools..."
	@if ! command -v opencode >/dev/null 2>&1; then \
		echo "Installing OpenCode..."; \
		curl -fsSL https://opencode.ai/install | bash; \
	else \
		echo "OpenCode already installed"; \
	fi
	@if ! command -v codex >/dev/null 2>&1; then \
		echo "Note: Codex CLI not found. Install manually if needed."; \
	else \
		echo "Codex already installed"; \
	fi
	@echo ""
	@echo "Step 10: Syncing AI configuration..."
	$(MAKE) ai
	@echo ""
	@echo "=== Setup complete ==="
	@echo "GAP version: $$(gap/gap --version 2>&1 | head -1 || echo 'Unknown')"
	@echo "Run 'make test' to verify installation"

# Install Python package
install:
	@echo "Installing gap-agent dependencies..."
	uv sync
	@echo "Installation complete"

# Update GAP to latest version in submodule
update-gap:
	@echo "=== Updating GAP submodule ==="
	git submodule update --remote gap
	cd gap && ./autogen.sh && ./configure && $(MAKE)
	cd gap && ./bin/BuildPackages.sh --strict || true
	@echo "=== GAP update complete ==="

# Clean all build artifacts
clean: clean-test
	@echo "=== Cleaning build artifacts ==="
	cd gap && $(MAKE) clean || true
	rm -rf build dist *.egg-info
	find . -type d -name __pycache__ -exec rm -rf {} + 2>/dev/null || true
	@echo "=== Clean complete ==="

# Test extraction on first 10 pages
extract-test:
	@echo "Extracting problems from first 10 pages..."
	@mkdir -p problems
	@uv run python src/extraction/extract_clean.py lit/1401.0300.pdf problems/test_problems.json 1 10
	@echo "Test extraction complete. Results in problems/test_problems.json"

# Extract all problems from entire PDF
extract-all:
	@echo "Extracting problems from entire PDF..."
	@mkdir -p problems
	@uv run python src/extraction/extract_clean.py lit/1401.0300.pdf problems/all_problems.json
	@echo "Full extraction complete. Results in problems/all_problems.json"

# Create individual problem folders from test extraction
problems-test: problems/test_problems.json
	@echo "Creating individual problem folders from test..."
	@uv run python -c '\
import json; \
from pathlib import Path; \
data = json.load(open("problems/test_problems.json")); \
[Path(f"problems/problem_{i+1}").mkdir(parents=True, exist_ok=True) or \
 Path(f"problems/problem_{i+1}/problem.json").write_text(json.dumps(p, indent=2)) \
 for i, p in enumerate(data)]'
	@echo "Created $$(ls -d problems/problem_* 2>/dev/null | wc -l | tr -d ' ') problem folders"

# Create individual problem folders from full extraction
problems: problems/all_problems.json
	@echo "Creating individual problem folders..."
	@uv run python -c '\
import json; \
from pathlib import Path; \
data = json.load(open("problems/all_problems.json")); \
[Path(f"problems/problem_{i+1}").mkdir(parents=True, exist_ok=True) or \
 Path(f"problems/problem_{i+1}/problem.json").write_text(json.dumps(p, indent=2)) \
 for i, p in enumerate(data)]'
	@echo "Created $$(ls -d problems/problem_* 2>/dev/null | wc -l | tr -d ' ') problem folders"

# Clean up generated problem files
clean-problems:
	rm -rf problems/
	rm -rf src/baml_client/

# Print open problems (no answer)
open:
	@uv run python make/print_problems.py open $(filter-out open,$(MAKECMDGOALS))

# Print closed problems (has answer)
closed:
	@uv run python make/print_problems.py closed $(filter-out closed,$(MAKECMDGOALS))

# Catch-all target to handle arguments like num=3 random=true
%:
	@:

# Help target
help:
	@echo "Available targets:"
	@echo ""
	@echo "Setup and Installation:"
	@echo "  setup      - Complete project setup (submodules, dependencies, GAP build)"
	@echo "  install    - Install Python dependencies"
	@echo "  update-gap - Update GAP to latest version and rebuild"
	@echo ""
	@echo "Testing:"
	@echo "  test            - Run all tests"
	@echo "  test-coverage   - Run tests with coverage report"
	@echo "  test-gap        - Run GAP interface tests only"
	@echo ""
	@echo "Documentation:"
	@echo "  ai      - Sync AGENTS.md to CLAUDE.md and .cursorrules"
	@echo "  readme  - Update README.md with project structure"
	@echo ""
	@echo "Problem Extraction:"
	@echo "  extract-test  - Extract problems from first 10 pages"
	@echo "  extract-all   - Extract all problems from PDF"
	@echo "  problems-test - Create problem folders from test extraction"
	@echo "  problems      - Create problem folders from full extraction"
	@echo "  open           - Print open problems (num=N random=true optional)"
	@echo "  closed         - Print closed problems (num=N random=true optional)"
	@echo ""
	@echo "Cleanup:"
	@echo "  clean          - Clean all build artifacts"
	@echo "  clean-test     - Clean test artifacts"
	@echo "  clean-problems - Clean up generated problem files"
	@echo ""
	@echo "  help    - Show this help message"