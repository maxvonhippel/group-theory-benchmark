.PHONY: formalize
formalize:
	@if [ -z "$(PROB)" ]; then \
		echo "Error: PROB not set. Usage: make formalize PROB=19.73"; \
		exit 1; \
	fi
	@echo "Formalizing problem $(PROB)..."
	@uv run python make/formalize_problem.py $(PROB)