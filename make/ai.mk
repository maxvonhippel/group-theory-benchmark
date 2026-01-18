# Manages AI assistant configuration and synchronization

# Sync AGENTS.md to CLAUDE.md and .cursorrules
.PHONY: ai
ai:
	@echo "Syncing AGENTS.md to CLAUDE.md and .cursorrules..."
	@cp AGENTS.md CLAUDE.md
	@cp AGENTS.md .cursorrules
	@echo "AI configuration files updated successfully"