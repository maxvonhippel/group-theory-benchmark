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

## Adding New Problem Sets

When adding a new problem set from `lit/`:

1. **Create BAML extraction logic** in `src/baml_src/functions.baml`:
   - Add a new function like `ExtractXxxProblems` following the pattern of `ExtractKourovkaProblems` and `ExtractKleeProblems`
   - Tailor the prompt to the specific problem numbering and format
   - Test on 10-20 pages before full extraction

2. **Update references.bib**:
   - Add a proper BibTeX entry for the source paper/book
   - Include URL if available online
   - Use appropriate BibTeX type (@book, @article, @misc, etc.)

3. **Update make/generate_readme.py**:
   - Add the new problem set to the "Problem Sets" section
   - Include title, author, and link (if available)
   - Format: `- **[Title](url)** by Author: Description`

4. **Extract problems**:
   - Use `make extract-all-xxx` or create a new target in `make/extract.mk`
   - Problems will be placed in `problems/{list_name}/`

5. **Regenerate README**:
   - Run `make readme` to update with new problem set
   - Verify the Problem Sets section includes the new entry
   - Verify references.bib is properly linked

The README generation automatically handles multiple problem lists and will show a "List" column in the solutions table when multiple lists are present.

## Common Tasks

- `make setup` - Initialize project (submodules, dependencies, GAP build)
- `make test` - Run test suite
- `make ai` - Sync AGENTS.md to CLAUDE.md and .cursorrules
- `make readme` - Update README.md with project structure