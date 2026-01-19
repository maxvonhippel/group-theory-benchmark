# Automated Claude solving targets

# Generate MCP config and launch Claude to solve a random problem
.PHONY: watch-solve
watch-solve:
	@echo "Setting up automated problem solving session..."
	@echo ""
	@echo "Generating MCP configuration..."
	@uv run python make/generate_mcp_config.py > /tmp/claude_mcp_config.json
	@echo "Selecting random open problem..."
	@uv run python make/generate_problem_prompt.py > /tmp/claude_problem_prompt.txt
	@echo ""
	@echo "Launching Claude (Opus) with MCP tools..."
	@echo "========================================"
	@echo ""
	@cat /tmp/claude_problem_prompt.txt
	@echo ""
	@echo "========================================"
	@echo ""
	@claude --model opus --mcp-config /tmp/claude_mcp_config.json "$$(cat /tmp/claude_problem_prompt.txt)"

# Just generate the prompt without launching
.PHONY: problem-prompt
problem-prompt:
	@uv run python make/generate_problem_prompt.py

# Just generate the MCP config
.PHONY: mcp-config
mcp-config:
	@uv run python make/generate_mcp_config.py