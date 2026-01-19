#!/usr/bin/env python3
"""
Generate MCP configuration for Claude CLI.
"""

import json
from pathlib import Path


def generate_mcp_config():
    """Generate MCP server configuration."""
    project_root = Path(__file__).parent.parent.absolute()
    
    config = {
        "mcpServers": {
            "gap-server": {
                "command": "uv",
                "args": ["run", "python", str(project_root / "src/tools/gap_mcp_server.py")],
                "cwd": str(project_root)
            },
            "lean-server": {
                "command": "uv",
                "args": ["run", "python", str(project_root / "src/tools/lean_mcp_server.py")],
                "cwd": str(project_root)
            }
        }
    }
    
    return json.dumps(config, indent=2)


if __name__ == '__main__':
    print(generate_mcp_config())