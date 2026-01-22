# Automated Claude solving targets

# Generate MCP config and launch Claude to solve a random problem
.PHONY: watch-solve
watch-solve:
	@echo "Setting up automated problem solving session..."
	@mkdir -p logs scratch/solutions
	@echo ""
	@echo "Generating MCP configuration..."
	@uv run python make/generate_mcp_config.py > /tmp/claude_mcp_config.json
	@echo "Selecting random open problem..."
	@uv run python make/generate_problem_prompt.py > /tmp/claude_problem_prompt.txt
	@PROBLEM_NUM=$$(grep -o 'problem #[0-9.]*' /tmp/claude_problem_prompt.txt | head -1 | sed 's/problem #//'); \
	PROBLEM_DIR="problems/$$PROBLEM_NUM"; \
	echo ""; \
	echo "Problem: #$$PROBLEM_NUM"; \
	echo "Problem directory: $$PROBLEM_DIR"; \
	echo ""; \
	echo "Creating problem directory..."; \
	mkdir -p "$$PROBLEM_DIR"; \
	echo "Launching Claude (Opus) with MCP tools..."; \
	echo "========================================"; \
	echo ""; \
	claude --model opus --mcp-config /tmp/claude_mcp_config.json --dangerously-skip-permissions < /tmp/claude_problem_prompt.txt; \
	echo ""; \
	echo "========================================"

# Just generate the prompt without launching
.PHONY: problem-prompt
problem-prompt:
	@uv run python make/generate_problem_prompt.py

# Just generate the MCP config
.PHONY: mcp-config
mcp-config:
	@uv run python make/generate_mcp_config.py