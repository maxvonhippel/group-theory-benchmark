#!/usr/bin/env python3
"""
Extract MCP tool information from server files for documentation.
"""

import ast
from pathlib import Path
from typing import Any


def extract_tools_from_file(filepath: Path) -> dict[str, Any]:
    """
    Extract tool information from an MCP server file.
    Returns dict with server name and list of tools.
    """
    with open(filepath, 'r') as f:
        content = f.read()
    
    tree = ast.parse(content)
    
    # Find the Server initialization to get server name
    server_name: str | None = None
    for node in ast.walk(tree):
        if isinstance(node, ast.Assign):
            for target in node.targets:
                if isinstance(target, ast.Name) and target.id == 'app':
                    if isinstance(node.value, ast.Call):
                        if isinstance(node.value.func, ast.Name) and node.value.func.id == 'Server':
                            if node.value.args:
                                server_name = ast.literal_eval(node.value.args[0])
    
    # Find the list_tools function
    tools: list[dict[str, Any]] = []
    for node in ast.walk(tree):
        if isinstance(node, ast.AsyncFunctionDef) and node.name == 'list_tools':
            # Look for return statement with list of Tool objects
            for stmt in ast.walk(node):
                if isinstance(stmt, ast.Return) and isinstance(stmt.value, ast.List):
                    for tool_call in stmt.value.elts:
                        if isinstance(tool_call, ast.Call):
                            tool_info: dict[str, Any] = {}
                            for keyword in tool_call.keywords:
                                if keyword.arg == 'name':
                                    tool_info['name'] = ast.literal_eval(keyword.value)
                                elif keyword.arg == 'description':
                                    tool_info['description'] = ast.literal_eval(keyword.value)
                            if tool_info:
                                tools.append(tool_info)
    
    return {
        'server': server_name or filepath.stem.replace('_mcp_server', '').upper(),
        'filepath': str(filepath),
        'tools': tools
    }


def format_tools_markdown(servers_info: list[dict[str, Any]]) -> str:
    """Format extracted tool information as markdown."""
    lines = []
    
    for server_info in servers_info:
        server_name = server_info['server']
        tools = server_info['tools']
        
        if not tools:
            continue
        
        lines.append(f"### {server_name.title()} MCP Server")
        lines.append("")
        lines.append(f"**Tools:** {len(tools)}")
        lines.append("")
        
        for i, tool in enumerate(tools, 1):
            name = tool.get('name', 'unknown')
            desc = tool.get('description', 'No description')
            
            # Clean up description - take first sentence or first line
            desc = desc.strip()
            if '\n' in desc:
                desc = desc.split('\n')[0]
            if '. ' in desc:
                desc = desc.split('. ')[0] + '.'
            
            lines.append(f"{i}. **`{name}`** - {desc}")
        
        lines.append("")
    
    return '\n'.join(lines)


def main() -> None:
    """Extract and print MCP tools documentation."""
    src_tools = Path(__file__).parent.parent / 'src' / 'tools'
    
    servers: list[dict[str, Any]] = []
    for mcp_file in sorted(src_tools.glob('*_mcp_server.py')):
        server_info = extract_tools_from_file(mcp_file)
        if server_info['tools']:
            servers.append(server_info)
    
    if not servers:
        print("No MCP tools found")
        return
    
    print(format_tools_markdown(servers))


if __name__ == '__main__':
    main()