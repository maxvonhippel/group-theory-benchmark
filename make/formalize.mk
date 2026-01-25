.PHONY: formalize
formalize:
	@# Check if batch mode (N parameter) or single mode (PROB parameter)
	@if [ -n "$(N)" ]; then \
		echo "Batch formalization mode: Processing first $(N) unformalized problems..."; \
		echo ""; \
		PROBLEMS=$$(uv run python make/find_unformalized.py $(N)); \
		if [ -z "$$PROBLEMS" ]; then \
			echo "No unformalized problems found."; \
			exit 0; \
		fi; \
		COUNT=0; \
		TOTAL=$$(echo "$$PROBLEMS" | wc -l | tr -d ' '); \
		for PROB in $$PROBLEMS; do \
			COUNT=$$((COUNT + 1)); \
			echo "========================================"; \
			echo "Formalization $$COUNT/$$TOTAL: Problem $$PROB"; \
			echo "========================================"; \
			uv run python make/formalize_problem.py $$PROB || echo "Failed to formalize $$PROB, continuing..."; \
			echo ""; \
		done; \
		echo "Batch formalization complete: $$COUNT problems processed."; \
	elif [ -n "$(PROB)" ]; then \
		echo "Formalizing problem $(PROB)..."; \
		uv run python make/formalize_problem.py $(PROB); \
	else \
		echo "Error: Either PROB or N must be set."; \
		echo "Usage:"; \
		echo "  make formalize PROB=19.73  # Formalize single problem"; \
		echo "  make formalize N=10         # Formalize first 10 unformalized problems"; \
		exit 1; \
	fi