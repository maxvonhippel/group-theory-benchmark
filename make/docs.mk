# Generates and updates documentation including README structure

# Update README.md with solution tracking
.PHONY: readme
readme:
	@echo "Generating README.md with solution tracking..."
	@uv run python make/generate_readme.py
	@echo "README.md has been updated"