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
	@TIMESTAMP=$$(date +%Y%m%d_%H%M%S); \
	PROBLEM_NUM=$$(grep -o 'problem #[0-9.]*' /tmp/claude_problem_prompt.txt | head -1 | sed 's/problem #//'); \
	SAFE_PROBLEM_NUM=$$(echo "$$PROBLEM_NUM" | tr '.' '_'); \
	SOLUTION_FILE="scratch/solutions/problem_$${SAFE_PROBLEM_NUM}.lean"; \
	LOGFILE="logs/$${TIMESTAMP}_problem_$${SAFE_PROBLEM_NUM}.log"; \
	echo ""; \
	echo "Problem: #$$PROBLEM_NUM"; \
	echo "Solution file: $$SOLUTION_FILE"; \
	echo "Log file: $$LOGFILE"; \
	echo ""; \
	echo "Launching Claude (Opus) with MCP tools..."; \
	echo "========================================"; \
	echo ""; \
	cat /tmp/claude_problem_prompt.txt; \
	echo ""; \
	echo "========================================"; \
	echo ""; \
	{ \
		echo "SESSION START: $$TIMESTAMP"; \
		echo ""; \
		cat /tmp/claude_problem_prompt.txt; \
		echo ""; \
		echo "========================================"; \
		echo ""; \
		cat /tmp/claude_problem_prompt.txt | stdbuf -oL claude --model opus --mcp-config /tmp/claude_mcp_config.json 2>&1; \
	} | tee "$$LOGFILE"; \
	echo "" | tee -a "$$LOGFILE"; \
	echo "SESSION END: $$(date +%Y%m%d_%H%M%S)" | tee -a "$$LOGFILE"; \
	echo "" | tee -a "$$LOGFILE"; \
	echo "" | tee -a "$$LOGFILE"; \
	echo "========================================" | tee -a "$$LOGFILE"; \
	echo "VALIDATING SOLUTION" | tee -a "$$LOGFILE"; \
	echo "========================================" | tee -a "$$LOGFILE"; \
	echo "" | tee -a "$$LOGFILE"; \
	if [ -f "$$SOLUTION_FILE" ]; then \
		echo "Solution file found: $$SOLUTION_FILE" | tee -a "$$LOGFILE"; \
		echo "" | tee -a "$$LOGFILE"; \
		if uv run python make/validate_lean_solution.py "$$SOLUTION_FILE" 2>&1 | tee -a "$$LOGFILE"; then \
			echo "" | tee -a "$$LOGFILE"; \
			echo "✓ SOLUTION VALIDATED SUCCESSFULLY" | tee -a "$$LOGFILE"; \
		else \
			echo "" | tee -a "$$LOGFILE"; \
			echo "✗ SOLUTION VALIDATION FAILED" | tee -a "$$LOGFILE"; \
		fi; \
	else \
		echo "✗ No solution file produced: $$SOLUTION_FILE" | tee -a "$$LOGFILE"; \
	fi

# Just generate the prompt without launching
.PHONY: problem-prompt
problem-prompt:
	@uv run python make/generate_problem_prompt.py

# Just generate the MCP config
.PHONY: mcp-config
mcp-config:
	@uv run python make/generate_mcp_config.py