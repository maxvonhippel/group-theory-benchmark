# Manages AI assistant configuration and synchronization

# Regenerate BAML client from source files
.PHONY: baml
baml:
	@echo "Regenerating BAML client from src/baml_src..."
	@uv run baml-cli generate --from ./src/baml_src
	@echo "BAML client updated"

# Sync AGENTS.md to CLAUDE.md and .cursorrules
.PHONY: ai
ai: baml
	@echo "Syncing AGENTS.md to CLAUDE.md and .cursorrules..."
	@cp AGENTS.md CLAUDE.md
	@cp AGENTS.md .cursorrules
	@echo "AI configuration files updated successfully"
