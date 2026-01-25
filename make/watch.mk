# Automated Claude solving targets

# Generate MCP config and launch Claude to solve problems
.PHONY: watch-solve
watch-solve:
	@mkdir -p logs scratch/solutions
	@echo "Generating MCP configuration..."
	@uv run python make/generate_mcp_config.py > /tmp/claude_mcp_config.json
	@# Batch mode or single mode
	@if [ -n "$(N)" ]; then \
		echo "Batch solving mode: Processing first $(N) unsolved problems..."; \
		echo ""; \
		PROBLEM_INDICES=$$(uv run python make/find_unsolved.py $(N)); \
		if [ -z "$$PROBLEM_INDICES" ]; then \
			echo "No unsolved problems found."; \
			exit 0; \
		fi; \
		COUNT=0; \
		TOTAL=$$(echo "$$PROBLEM_INDICES" | wc -l | tr -d ' '); \
		for PROBLEM_INDEX in $$PROBLEM_INDICES; do \
			COUNT=$$((COUNT + 1)); \
			echo ""; \
			echo "========================================"; \
			echo "Solving $$COUNT/$$TOTAL: Problem Index $$PROBLEM_INDEX"; \
			echo "========================================"; \
			$(MAKE) watch-solve-single PROBLEM_INDEX=$$PROBLEM_INDEX || echo "Failed on problem $$PROBLEM_INDEX, continuing..."; \
		done; \
		echo ""; \
		echo "Batch solving complete: $$COUNT problems processed."; \
	else \
		echo "Setting up automated problem solving session..."; \
		echo "Selecting random open problem..."; \
		$(MAKE) watch-solve-single; \
	fi

# Internal target for solving a single problem
.PHONY: watch-solve-single
watch-solve-single:
	@if [ -n "$(PROBLEM_INDEX)" ]; then \
		uv run python -c "from make.generate_problem_prompt import generate_prompt, load_open_problems; \
			problems = load_open_problems(); \
			p_idx = int('$(PROBLEM_INDEX)'); \
			problem = next((p for i, p in problems if i == p_idx), None); \
			if problem: print(generate_prompt(p_idx, problem))" > /tmp/claude_problem_prompt.txt; \
	else \
		uv run python make/generate_problem_prompt.py > /tmp/claude_problem_prompt.txt; \
	fi; \
	if grep -q '^ALREADY_SOLVED:' /tmp/claude_problem_prompt.txt; then \
		SOLUTION_PATH=$$(cat /tmp/claude_problem_prompt.txt | sed 's/^ALREADY_SOLVED://'); \
		echo "Problem already has a solution at: $$SOLUTION_PATH"; \
		echo "Skipping."; \
		exit 0; \
	fi; \
	PROBLEM_INDEX=$$(grep -o 'stored as problem_[0-9]*' /tmp/claude_problem_prompt.txt | head -1 | sed 's/stored as problem_//'); \
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
	echo "Problem index: $$PROBLEM_INDEX"; \
	echo "Problem directory: $$PROBLEM_DIR"; \
	echo "AI Backend: $$AI_BACKEND"; \
	echo ""; \
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