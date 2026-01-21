#!/usr/bin/env python3
"""
Generate a prompt from a random open problem for Claude to solve.
"""

import ast
import json
import random
from pathlib import Path


def load_open_problems():
    """Load all open problems."""
    problems_file = Path(__file__).parent.parent / "problems/all_problems.json"
    with open(problems_file) as f:
        data = json.load(f)
    return [p for p in data if not p.get('answer')]


def extract_tool_docs(mcp_server_path):
    """Extract tool documentation from an MCP server file using AST."""
    with open(mcp_server_path) as f:
        content = f.read()
    
    tree = ast.parse(content)
    tools = []
    
    # Find the list_tools function
    for node in ast.walk(tree):
        if isinstance(node, ast.AsyncFunctionDef) and node.name == 'list_tools':
            # Look for return statement with list of Tool objects
            for stmt in ast.walk(node):
                if isinstance(stmt, ast.Return) and isinstance(stmt.value, ast.List):
                    for tool_call in stmt.value.elts:
                        if isinstance(tool_call, ast.Call):
                            tool_name = None
                            tool_desc = None
                            for keyword in tool_call.keywords:
                                if keyword.arg == 'name':
                                    tool_name = ast.literal_eval(keyword.value)
                                elif keyword.arg == 'description':
                                    tool_desc = ast.literal_eval(keyword.value)
                            
                            if tool_name and tool_desc:
                                # Get first sentence
                                desc = tool_desc.strip()
                                if '. ' in desc:
                                    desc = desc.split('. ')[0] + '.'
                                tools.append(f"  - `{tool_name}`: {desc}")
    
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
    project_root = Path(__file__).parent.parent
    # Sanitize problem number for filename (replace dots with underscores, remove trailing periods)
    safe_problem_num = str(problem_num).replace('.', '_').rstrip('_')
    solution_file = f"scratch/solutions/problem_{safe_problem_num}.lean"
    
    # Get tool documentation
    tool_docs = generate_tool_documentation()
    
    prompt = f"""You are solving Kourovka Notebook problem #{problem_num}.

**Problem Statement:**
{problem_text}

**Your Goal:**
Produce a VERIFIED formal proof in Lean 4 that solves this problem.

**Success Criteria:**
1. Write a complete Lean proof to: {solution_file}
2. The proof must compile without errors
3. No 'sorry', 'admit', or axioms allowed
4. Must include actual theorem/lemma statements and proofs

**For Open/Unsolvable Problems:**
If this is an open research problem with no known solution:
1. Declare it unsolvable and explain why
2. Provide a formalization of the problem statement in Lean (definitions, types)
3. Optionally include partial results or related lemmas
4. The formalization must still compile without 'sorry'

**How Your Work Will Be Tested:**
After you finish, the system will run:
```bash
lean {solution_file}
```

The solution is considered successful if:
- The file compiles with exit code 0
- Contains no 'sorry' or 'admit' 
- Contains either: a complete proof OR a formalization with unsolvability declaration

DO NOT EXIT until either:
1. Your solution passes these tests, OR
2. You explicitly declare you cannot solve the problem (with formalization)

{tool_docs}

**Required Workflow:**
1. Use GAP tools to explore the problem computationally
2. Use Lean tools to develop and verify your formal proof
3. Iteratively refine until the proof compiles without errors
4. Use `verify_proof` to confirm your solution before finishing

**Important:**
- Natural language proofs DO NOT count - you must produce verified Lean code
- Test your proof multiple times with `verify_proof` before declaring success
- If you find a counterexample with GAP, formalize it in Lean as a counterexample proof

Begin your investigation now. Use the tools actively."""

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