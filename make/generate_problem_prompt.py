#!/usr/bin/env python3
"""
Generate a prompt from a random open problem for Claude to solve.
"""

import json
import random
import re
from pathlib import Path


def load_open_problems():
    """Load all open problems."""
    problems_file = Path(__file__).parent.parent / "problems/all_problems.json"
    with open(problems_file) as f:
        data = json.load(f)
    return [p for p in data if not p.get('answer')]


def extract_tool_docs(mcp_server_path):
    """Extract tool documentation from an MCP server file."""
    with open(mcp_server_path) as f:
        content = f.read()
    
    tools = []
    
    # Find all tool definitions
    tool_pattern = r'@server\.call_tool\(\)\s+async def (\w+)\((.*?)\):'
    doc_pattern = r'"""(.*?)"""'
    
    for match in re.finditer(tool_pattern, content, re.DOTALL):
        tool_name = match.group(1)
        
        # Find the docstring after the function definition
        func_start = match.end()
        remaining = content[func_start:func_start+2000]
        doc_match = re.search(doc_pattern, remaining, re.DOTALL)
        
        if doc_match:
            docstring = doc_match.group(1).strip()
            # Get first paragraph only
            first_para = docstring.split('\n\n')[0].replace('\n', ' ')
            tools.append(f"  - `{tool_name}`: {first_para}")
    
    return tools


def generate_tool_documentation():
    """Generate documentation for all available MCP tools."""
    project_root = Path(__file__).parent.parent
    
    gap_tools = extract_tool_docs(project_root / "src/tools/gap_mcp_server.py")
    lean_tools = extract_tool_docs(project_root / "src/tools/lean_mcp_server.py")
    
    doc = "**Available MCP Tools:**\n\n"
    
    if gap_tools:
        doc += "GAP Server (computational group theory):\n"
        doc += "\n".join(gap_tools) + "\n\n"
    
    if lean_tools:
        doc += "Lean Server (formal theorem proving):\n"
        doc += "\n".join(lean_tools)
    
    return doc


def generate_prompt(problem):
    """Generate a solving prompt for Claude."""
    problem_num = problem.get('problem_number', 'unknown')
    problem_text = problem.get('problem_text', 'No problem text')
    
    # Get tool documentation
    tool_docs = generate_tool_documentation()
    
    prompt = f"""You are solving Kourovka Notebook problem #{problem_num}.

**Problem Statement:**
{problem_text}

**Your Task:**
Use the available MCP tools to attempt to solve this problem.

{tool_docs}

**Approach:**
1. Analyze the problem and determine if it's amenable to computational or formal methods
2. Use GAP to search for counterexamples or gather computational evidence
3. Use Lean to formalize and prove results if possible
4. Report your findings - counterexample, proof, or explanation of where you got stuck

Work step-by-step. Begin your investigation now."""

    return prompt


def main():
    """Generate and print prompt for a random open problem."""
    problems = load_open_problems()
    if not problems:
        print("Error: No open problems found")
        return
    
    problem = random.choice(problems)
    prompt = generate_prompt(problem)
    print(prompt)


if __name__ == '__main__':
    main()