.PHONY: formalize
formalize:
	@if [ -z "$(PROB)" ]; then \
		echo "Error: PROB argument required. Usage: make formalize PROB=19.73"; \
		exit 1; \
	fi
	@echo "=== Formalizing Problem #$(PROB) in Lean ==="
	@uv run python make/formalize_problem.py $(PROB)