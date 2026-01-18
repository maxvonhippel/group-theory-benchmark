"""
Test the MCP server directly via the protocol.
"""

import json
import subprocess
import sys


def call_mcp_tool(tool_name: str, arguments: dict):
    """Call an MCP tool and return the result."""
    # Start the MCP server
    proc = subprocess.Popen(
        ["uv", "run", "python", "src/tools/gap_mcp_server.py"],
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True
    )

    # Send the call_tool request
    request = {
        "jsonrpc": "2.0",
        "id": 1,
        "method": "tools/call",
        "params": {
            "name": tool_name,
            "arguments": arguments
        }
    }

    proc.stdin.write(json.dumps(request) + "\n")
    proc.stdin.flush()

    # Read response
    response_line = proc.stdout.readline()
    proc.terminate()

    return json.loads(response_line)


def test_query_gap():
    """Test the query_gap tool."""
    print("=" * 80)
    print("Testing query_gap tool via MCP protocol")
    print("=" * 80)

    test_cases = [
        "What is the order of the center of S_4?",
        "Is A_5 simple?",
        "How many groups of order 8 are there?",
    ]

    for query in test_cases:
        print(f"\nQuery: {query}")
        try:
            result = call_mcp_tool("query_gap", {"question": query})
            print(f"Result: {json.dumps(result, indent=2)}")
        except Exception as e:
            print(f"Error: {e}")
        print("-" * 80)


def test_check_property():
    """Test the check_group_property tool."""
    print("\n" + "=" * 80)
    print("Testing check_group_property tool via MCP protocol")
    print("=" * 80)

    test_cases = [
        ("SymmetricGroup(4)", "abelian"),
        ("AlternatingGroup(5)", "simple"),
        ("CyclicGroup(12)", "cyclic"),
    ]

    for group_expr, prop in test_cases:
        print(f"\nCheck: {group_expr} is {prop}?")
        try:
            result = call_mcp_tool("check_group_property", {
                "group_expression": group_expr,
                "property": prop
            })
            print(f"Result: {json.dumps(result, indent=2)}")
        except Exception as e:
            print(f"Error: {e}")
        print("-" * 80)


if __name__ == "__main__":
    test_query_gap()
    test_check_property()
