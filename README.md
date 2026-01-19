# GAP Agent

A computational group theory agent powered by [GAP (Groups, Algorithms, Programming)](https://www.gap-system.org/).

**Inspired by:** [Using GAP to find counterexamples in topology](https://arxiv.org/pdf/2107.06982) - This paper demonstrates how computational algebra systems like GAP can systematically search for counterexamples to mathematical conjectures. The authors used GAP's SmallGroup library to discover the first counterexamples to the free extension conjecture, specifically groups of order 243.

## Structure

The structure of this project is organized as follows:

```
gap-agent/
├── examples
│   ├── demo_gap_mcp.py  # Demo script showing how to use the GAP MCP server tools.
│   ├── test_mcp_real_problems.py  # Test the GAP MCP on real Kourovka Notebook problems.
│   ├── test_mcp_server.py  # Test the MCP server directly via the protocol.
│   └── test_query_agent.py  # Test the GAP query agent with diverse natural language queries.
├── gap
│   ├── doc
│   ├── lib
│   └── gap
├── lit
│   └── 1401.0300.pdf
├── make
│   ├── ai.mk
│   ├── docs.mk
│   ├── print_problems.py  # Print open or closed problems from the extraction.
│   ├── tests.mk
│   └── tree_with_comments.py  # Generate a tree structure of the project with comments from Python files.
├── pkg
├── src
│   ├── baml_src
│   │   ├── clients.baml
│   │   ├── functions.baml
│   │   ├── generators.baml
│   │   └── types.baml
│   ├── extraction
│   │   ├── clean_json.py
│   │   ├── extract.py
│   │   └── extract_clean.py
│   └── tools
│       ├── gap.py  # Python interface to GAP (Groups, Algorithms, Programming) system.
│       ├── gap_mcp_server.py  # GAP MCP Server - Model Context Protocol server for GAP (Groups, Algorithms, Programming).
│       ├── gap_query_agent.py  # GAP Query Agent - Iteratively generates and executes GAP code from English queries.
│       └── test_gap.py
├── tests
│   ├── test_gap.py  # Tests for GAP Python interface.
│   └── test_gap_mcp.py  # Tests for the GAP MCP server.
├── .cursorrules
├── AGENTS.md
├── CLAUDE.md
├── MCP_README.md
├── Makefile
├── README.md
├── pyproject.toml
└── tree_output.tmp
```

## Problems

This project contains extracted math problems from the Kourovka Notebook:

- **Open problems:** 1237
- **Closed problems (with answers):** 763
- **Total problems:** 2000

### Viewing Problems

Use `make open` to view open problems (no answer) or `make closed` to view closed problems (with answers).

**Options:**

- `num=N` - Limit output to N problems
- `random=true` - Select problems randomly (requires num= to be specified)

**Examples:**

```bash
# View all open problems
make open

# View first 5 open problems
make open num=5

# View 3 random open problems
make open num=3 random=true

# View all closed problems (with answers)
make closed

# View 10 random closed problems
make closed num=10 random=true
```

## Using the MCP Server

The GAP MCP (Model Context Protocol) server provides AI agents with tools to explore group theory computationally.

### Starting the MCP Server

```bash
uv run python src/tools/gap_mcp_server.py
```

### Available MCP Tools

1. **query_gap** - Natural language queries (no GAP knowledge required)
   ```python
   # Example: "What is the order of the center of S_4?"
   # Example: "How many non-abelian groups of order 16 exist?"
   ```

2. **check_group_property** - Check if a group has a property
   ```python
   # Properties: abelian, cyclic, simple, solvable, nilpotent, perfect
   ```

3. **compute_group_invariants** - Get group invariants (order, center, etc.)

4. **find_counterexample** - Search for groups violating a property

5. **search_small_groups** - Filter groups by multiple criteria

6. **compare_groups** - Check if two groups are isomorphic

7. **evaluate_gap** - Execute raw GAP code (for advanced users)

### Python Usage

```python
from src.tools.gap_query_agent import query_gap

# Ask questions in natural language
result = query_gap("Is the alternating group A_5 simple?")
print(result.result_value)  # True
print(result.final_code)    # IsSimple(AlternatingGroup(5));
```

See `examples/test_query_agent.py` and `examples/test_mcp_real_problems.py` for more examples.

