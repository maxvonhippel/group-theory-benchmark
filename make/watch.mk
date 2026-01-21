# Automated Claude solving targets

# Generate MCP config and launch Claude to solve a random problem
.PHONY: watch-solve
watch-solve:
	@echo "Setting up automated problem solving session..."
	@mkdir -p logs
	@echo ""
	@echo "Generating MCP configuration..."
	@uv run python make/generate_mcp_config.py > /tmp/claude_mcp_config.json
	@echo "Selecting random open problem..."
	@uv run python make/generate_problem_prompt.py > /tmp/claude_problem_prompt.txt
	@TIMESTAMP=$$(date +%Y%m%d_%H%M%S); \
	PROBLEM_NUM=$$(grep -o 'problem #[0-9.]*' /tmp/claude_problem_prompt.txt | head -1 | sed 's/problem #//'); \
	LOGFILE="logs/$${TIMESTAMP}_problem_$${PROBLEM_NUM}.log"; \
	echo ""; \
	echo "Launching Claude (Opus) with MCP tools..."; \
	echo "Trace will be saved to: $$LOGFILE"; \
	echo "========================================"; \
	echo ""; \
	cat /tmp/claude_problem_prompt.txt; \
	echo ""; \
	echo "========================================"; \
	echo ""; \
	echo "SESSION START: $$TIMESTAMP" | tee "$$LOGFILE"; \
	echo "" | tee -a "$$LOGFILE"; \
	cat /tmp/claude_problem_prompt.txt | tee -a "$$LOGFILE"; \
	echo "" | tee -a "$$LOGFILE"; \
	echo "========================================" | tee -a "$$LOGFILE"; \
	echo "" | tee -a "$$LOGFILE"; \
	cat /tmp/claude_problem_prompt.txt | claude --model opus --mcp-config /tmp/claude_mcp_config.json 2>&1 | tee -a "$$LOGFILE"; \
	echo "" | tee -a "$$LOGFILE"; \
	echo "SESSION END: $$(date +%Y%m%d_%H%M%S)" | tee -a "$$LOGFILE"

# Just generate the prompt without launching
.PHONY: problem-prompt
problem-prompt:
	@uv run python make/generate_problem_prompt.py

# Just generate the MCP config
.PHONY: mcp-config
mcp-config:
	@uv run python make/generate_mcp_config.py