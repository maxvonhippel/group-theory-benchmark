# Agent Rules

Always use `uv`, e.g., `uv add ...` or `uv run ...`.
Always use full-path imports (no relative imports).
Never use shebangs (#!/usr/bin/env python3) in Python files since we use uv run.
Don't use ".." for types in Python. Use proper type hints like `-> GapResult` not `-> "GapResult"`.

## Project Organization

This is an AI agent for solving abstract algebra problems using GAP (Groups, Algorithms, Programming).

### Directory Structure

- `src/` - Main source code
  - `tools/` - GAP Python interface and utilities
  - `baml_client/` - Generated BAML client code (if using BAML)
  - `baml_src/` - BAML source files (if using BAML)
- `gap/` - GAP system installation (git submodule)
- `examples/` - Example scripts and usage demonstrations
- `problems/` - Problem sets and test cases
- `make/` - Makefile scripts and utilities
- `tests/` - Test suite

### Scripts

Scripts used by Makefiles belong in `make/` directory (e.g., `make/tree_with_comments.py`, `make/run_tests.py`).

## GAP Interface

The GAP interface (`src/tools/gap.py`) uses subprocess mode to communicate with GAP.
This approach is reliable and works with any GAP installation without requiring additional compiled extensions.

Key features:
- Automatic filtering of GAP initialization warnings
- Type conversion for common types (int, bool, string)
- Convenience methods for group theory operations
- Clean result objects with success/error handling

## Testing

Tests should be placed in `tests/` directory.
Run tests with `make test` or `uv run pytest`.

## Common Tasks

- `make setup` - Initialize project (submodules, dependencies, GAP build)
- `make test` - Run test suite
- `make ai` - Sync AGENTS.md to CLAUDE.md and .cursorrules
- `make readme` - Update README.md with project structure