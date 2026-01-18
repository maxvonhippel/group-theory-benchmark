# Generates and updates documentation including README structure

# Update README.md with tree structure
.PHONY: readme
readme:
	@echo "Generating project tree structure..."
	@uv run python make/tree_with_comments.py 2>/dev/null > tree_output.tmp || echo "Warning: tree generation failed"
	@if [ -f tree_output.tmp ]; then \
		awk '/^## (Structure|Problems|Using the MCP Server)$$/{exit} {print}' README.md > README.md.new 2>/dev/null || touch README.md.new; \
		echo '## Structure' >> README.md.new; \
		echo '' >> README.md.new; \
		echo 'The structure of this project is organized as follows:' >> README.md.new; \
		echo '' >> README.md.new; \
		echo '```' >> README.md.new; \
		cat tree_output.tmp >> README.md.new; \
		echo '```' >> README.md.new; \
		echo '' >> README.md.new; \
		if [ -f problems/all_problems.json ]; then \
			echo '## Problems' >> README.md.new; \
			echo '' >> README.md.new; \
			echo 'This project contains extracted math problems from the Kourovka Notebook:' >> README.md.new; \
			echo '' >> README.md.new; \
			uv run python -c "import json; data=json.load(open('problems/all_problems.json')); open_count=len([p for p in data if not p.get('answer')]); closed_count=len([p for p in data if p.get('answer')]); print(f'- **Open problems:** {open_count}'); print(f'- **Closed problems (with answers):** {closed_count}'); print(f'- **Total problems:** {len(data)}')" >> README.md.new; \
			echo '' >> README.md.new; \
			echo '### Viewing Problems' >> README.md.new; \
			echo '' >> README.md.new; \
			echo 'Use `make open` to view open problems (no answer) or `make closed` to view closed problems (with answers).' >> README.md.new; \
			echo '' >> README.md.new; \
			echo '**Options:**' >> README.md.new; \
			echo '' >> README.md.new; \
			echo '- `num=N` - Limit output to N problems' >> README.md.new; \
			echo '- `random=true` - Select problems randomly (requires num= to be specified)' >> README.md.new; \
			echo '' >> README.md.new; \
			echo '**Examples:**' >> README.md.new; \
			echo '' >> README.md.new; \
			echo '```bash' >> README.md.new; \
			echo '# View all open problems' >> README.md.new; \
			echo 'make open' >> README.md.new; \
			echo '' >> README.md.new; \
			echo '# View first 5 open problems' >> README.md.new; \
			echo 'make open num=5' >> README.md.new; \
			echo '' >> README.md.new; \
			echo '# View 3 random open problems' >> README.md.new; \
			echo 'make open num=3 random=true' >> README.md.new; \
			echo '' >> README.md.new; \
			echo '# View all closed problems (with answers)' >> README.md.new; \
			echo 'make closed' >> README.md.new; \
			echo '' >> README.md.new; \
			echo '# View 10 random closed problems' >> README.md.new; \
			echo 'make closed num=10 random=true' >> README.md.new; \
			echo '```' >> README.md.new; \
			echo '' >> README.md.new; \
		fi; \
		echo '## Using the MCP Server' >> README.md.new; \
		echo '' >> README.md.new; \
		echo 'The GAP MCP (Model Context Protocol) server provides AI agents with tools to explore group theory computationally.' >> README.md.new; \
		echo '' >> README.md.new; \
		echo '### Starting the MCP Server' >> README.md.new; \
		echo '' >> README.md.new; \
		echo '```bash' >> README.md.new; \
		echo 'uv run python src/tools/gap_mcp_server.py' >> README.md.new; \
		echo '```' >> README.md.new; \
		echo '' >> README.md.new; \
		echo '### Available MCP Tools' >> README.md.new; \
		echo '' >> README.md.new; \
		echo '1. **query_gap** - Natural language queries (no GAP knowledge required)' >> README.md.new; \
		echo '   ```python' >> README.md.new; \
		echo '   # Example: "What is the order of the center of S_4?"' >> README.md.new; \
		echo '   # Example: "How many non-abelian groups of order 16 exist?"' >> README.md.new; \
		echo '   ```' >> README.md.new; \
		echo '' >> README.md.new; \
		echo '2. **check_group_property** - Check if a group has a property' >> README.md.new; \
		echo '   ```python' >> README.md.new; \
		echo '   # Properties: abelian, cyclic, simple, solvable, nilpotent, perfect' >> README.md.new; \
		echo '   ```' >> README.md.new; \
		echo '' >> README.md.new; \
		echo '3. **compute_group_invariants** - Get group invariants (order, center, etc.)' >> README.md.new; \
		echo '' >> README.md.new; \
		echo '4. **find_counterexample** - Search for groups violating a property' >> README.md.new; \
		echo '' >> README.md.new; \
		echo '5. **search_small_groups** - Filter groups by multiple criteria' >> README.md.new; \
		echo '' >> README.md.new; \
		echo '6. **compare_groups** - Check if two groups are isomorphic' >> README.md.new; \
		echo '' >> README.md.new; \
		echo '7. **evaluate_gap** - Execute raw GAP code (for advanced users)' >> README.md.new; \
		echo '' >> README.md.new; \
		echo '### Python Usage' >> README.md.new; \
		echo '' >> README.md.new; \
		echo '```python' >> README.md.new; \
		echo 'from src.tools.gap_query_agent import query_gap' >> README.md.new; \
		echo '' >> README.md.new; \
		echo '# Ask questions in natural language' >> README.md.new; \
		echo 'result = query_gap("Is the alternating group A_5 simple?")' >> README.md.new; \
		echo 'print(result.result_value)  # True' >> README.md.new; \
		echo 'print(result.final_code)    # IsSimple(AlternatingGroup(5));' >> README.md.new; \
		echo '```' >> README.md.new; \
		echo '' >> README.md.new; \
		echo 'See `examples/test_query_agent.py` and `examples/test_mcp_real_problems.py` for more examples.' >> README.md.new; \
		echo '' >> README.md.new; \
		if grep -q "^## " README.md 2>/dev/null; then \
			awk 'BEGIN{found=0} /^## (Structure|Problems|Using the MCP Server)$$/{found=1; next} found && /^## /{found=0} !found && /^## /{print}' README.md >> README.md.new; \
		fi; \
		mv README.md.new README.md; \
		rm -f tree_output.tmp; \
		echo "README.md updated with tree structure and problem statistics"; \
	else \
		echo "Could not generate tree structure - tree_with_comments.py may not exist yet"; \
	fi
