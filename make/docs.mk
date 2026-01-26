# Generates and updates documentation including README structure

# Update README.md with solution tracking
.PHONY: readme
readme:
	@echo "Generating README.md..."
	@LIST=$${LIST:-}; \
	if [ -n "$$LIST" ]; then \
		uv run python make/generate_readme.py --list $$LIST; \
	else \
		uv run python make/generate_readme.py; \
	fi
	@echo "README.md updated"