#!/usr/bin/env python3
"""
Generate MCP configuration for Claude CLI.
"""

import json
from pathlib import Path


def generate_mcp_config():
    """Generate MCP server configuration."""
    project_root = Path(__file__).parent.parent.absolute()
    
    # Note: Lean 4 theorem proving is provided via Claude Code plugins
    # (lean4-skills from cameronfreer/lean4-skills), not MCP servers.
    # Install with: claude plugin marketplace add cameronfreer/lean4-skills
    #               claude plugin install lean4-theorem-proving@lean4-skills
    config = {
        "mcpServers": {
            "gap-server": {
                "command": "uv",
                "args": ["run", "python", "-m", "src.tools.gap_mcp_server"],
                "cwd": str(project_root)
            }
        }
    }
    
    return json.dumps(config, indent=2)


if __name__ == '__main__':
    print(generate_mcp_config())