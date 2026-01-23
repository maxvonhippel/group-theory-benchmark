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
	@uv run python make/generate_problem_prompt.py > /tmp/claude_problem_prompt.txt; \
	if grep -q '^ALREADY_SOLVED:' /tmp/claude_problem_prompt.txt; then \
		SOLUTION_PATH=$$(cat /tmp/claude_problem_prompt.txt | sed 's/^ALREADY_SOLVED://'); \
		echo ""; \
		echo "Problem already has a solution at: $$SOLUTION_PATH"; \
		echo "Skipping Claude invocation."; \
		exit 0; \
	fi
	@PROBLEM_INDEX=$$(grep -o 'stored as problem_[0-9]*' /tmp/claude_problem_prompt.txt | head -1 | sed 's/stored as problem_//'); \
	PROBLEM_DIR="problems/problem_$$PROBLEM_INDEX"; \
	AI_BACKEND="claude"; \
	AI_MODEL="opus"; \
	if echo "$(ARGS)" | grep -q -- '--codex'; then \
		AI_BACKEND="codex"; \
		AI_MODEL=""; \
	elif echo "$(ARGS)" | grep -q -- '--opencode'; then \
		AI_BACKEND="opencode"; \
		AI_MODEL=""; \
	fi; \
	echo ""; \
	echo "Problem index: $$PROBLEM_INDEX"; \
	echo "Problem directory: $$PROBLEM_DIR"; \
	echo "AI Backend: $$AI_BACKEND"; \
	echo ""; \
	echo "Creating problem directory..."; \
	mkdir -p "$$PROBLEM_DIR"; \
	echo "Launching $$AI_BACKEND with MCP tools..."; \
	echo "========================================"; \
	echo ""; \
	if [ "$$AI_BACKEND" = "claude" ]; then \
		claude --model opus --mcp-config /tmp/claude_mcp_config.json --dangerously-skip-permissions < /tmp/claude_problem_prompt.txt; \
	elif [ "$$AI_BACKEND" = "codex" ]; then \
		codex --mcp-config /tmp/claude_mcp_config.json < /tmp/claude_problem_prompt.txt; \
	elif [ "$$AI_BACKEND" = "opencode" ]; then \
		opencode --mcp-config /tmp/claude_mcp_config.json < /tmp/claude_problem_prompt.txt; \
	fi; \
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