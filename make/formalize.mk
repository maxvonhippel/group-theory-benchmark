.PHONY: formalize
formalize:
	@# Check if batch mode (N parameter) or single mode (PROB parameter)
	@if [ -n "$(N)" ]; then \
		LIST=$${LIST:-kourovka}; \
		echo "Batch formalization mode: Processing first $(N) unformalized problems from $$LIST..."; \
		echo ""; \
		PROBLEMS=$$(uv run python make/find_unformalized.py $(N) --list $$LIST); \
		if [ -z "$$PROBLEMS" ]; then \
			echo "No unformalized problems found."; \
			exit 0; \
		fi; \
		COUNT=0; \
		TOTAL=$$(echo "$$PROBLEMS" | wc -l | tr -d ' '); \
		for PROB in $$PROBLEMS; do \
			COUNT=$$((COUNT + 1)); \
			echo "========================================"; \
			echo "Formalization $$COUNT/$$TOTAL: Problem $$PROB (list: $$LIST)"; \
			echo "========================================"; \
			uv run python make/formalize_problem.py $$PROB --list $$LIST || echo "Failed to formalize $$PROB, continuing..."; \
			echo ""; \
		done; \
		echo "Batch formalization complete: $$COUNT problems processed."; \
		echo "Updating README.md..."; \
		$(MAKE) readme; \
	elif [ -n "$(PROB)" ]; then \
		LIST=$${LIST:-kourovka}; \
		echo "Formalizing problem $(PROB) from list $$LIST..."; \
		uv run python make/formalize_problem.py $(PROB) --list $$LIST; \
		if [ $$? -eq 0 ]; then \
			echo "Updating README.md..."; \
			$(MAKE) readme; \
		fi; \
	else \
		echo "Error: Either PROB or N must be set."; \
		echo "Usage:"; \
		echo "  make formalize PROB=19.73 [LIST=kourovka]  # Formalize single problem"; \
		echo "  make formalize N=10 [LIST=kourovka]        # Formalize first 10 unformalized problems"; \
		exit 1; \
	fi