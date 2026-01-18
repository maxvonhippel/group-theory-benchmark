## Structure

The structure of this project is organized as follows:

```
gap-agent/
├── gap
│   ├── doc
│   ├── gap
│   │   ├── doc
│   │   └── lib
│   └── lib
├── lit
│   └── 1401.0300.pdf
├── make
│   ├── ai.mk
│   ├── docs.mk
│   ├── print_problems.py  # Print open or closed problems from the extraction.
│   ├── tests.mk
│   └── tree_with_comments.py  # Generate a tree structure of the project with comments from Python files.
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
│       └── test_gap.py
├── tests
│   └── test_gap.py  # Tests for GAP Python interface.
├── .cursorrules
├── AGENTS.md
├── CLAUDE.md
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

