#!/usr/bin/env python3
"""
Generate a prompt from a random open problem for Claude to solve.
"""

import ast
import json
import random
import sys
from pathlib import Path


# Solution artifact files - if any exists, problem is considered solved
SOLUTION_ARTIFACTS = [
    'disproof.py',
    'proof.lean',
    'problem.lean',
    'formalization_attempt_summary.txt',
]


def get_problem_dir(problem_num: str) -> Path:
    """Get the directory path for a problem."""
    return Path(__file__).parent.parent / "problems" / problem_num


def is_problem_solved(problem_num: str) -> tuple[bool, str | None]:
    """Check if a problem already has a solution artifact.

    Returns:
        (is_solved, artifact_path) - True and path if solved, False and None otherwise
    """
    problem_dir = get_problem_dir(problem_num)
    for artifact in SOLUTION_ARTIFACTS:
        artifact_path = problem_dir / artifact
        if artifact_path.exists():
            return True, str(artifact_path)
    return False, None


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
    problem_dir = f"problems/{problem_num}"

    # Get tool documentation
    tool_docs = generate_tool_documentation()

    prompt = f"""You are solving Kourovka Notebook problem #{problem_num}.

**Problem Statement:**
{problem_text}

**Your Goal:**
Determine if this problem can be solved, and produce the appropriate artifact.

**Output Directory:**
{problem_dir}/

**Four Possible Outcomes:**

1. **Found a Counterexample (via GAP)**
   - Write Python/GAP code to: {problem_dir}/disproof.py
   - Must generate and verify a concrete counterexample
   - Include comments explaining why it's a counterexample

2. **Proved the Theorem (via Lean)**
   - Write Lean proof to: {problem_dir}/proof.lean
   - Must compile without errors
   - No 'sorry' or 'admit' allowed

3. **Formalized but Unsolved**
   - Write formalization to: {problem_dir}/problem.lean
   - Include definitions, types, and problem statement
   - Use 'sorry' for unsolved parts
   - Add comments explaining what you tried and why it's hard

4. **Could Not Formalize**
   - Write summary to: {problem_dir}/formalization_attempt_summary.txt
   - Use this when the problem is too open-ended, vague, or requires
     mathematical infrastructure beyond what's available in Lean
   - Explain what aspects made formalization difficult
   - Document any partial progress or insights gained
   - This is a valid outcome for problems that are inherently hard to state formally

{tool_docs}

**Workflow:**
1. Use GAP tools to search for counterexamples first
2. If no counterexample found, attempt Lean proof
3. If proof is too difficult, provide formalization with sorry
4. If formalization itself is infeasible, write formalization_attempt_summary.txt

**Success Criteria:**
- Exactly ONE of: disproof.py, proof.lean, problem.lean, or formalization_attempt_summary.txt exists when done
- File compiles/runs without errors (except sorry in problem.lean)
- Clear explanation of your approach

DO NOT EXIT until you have created one artifact file in {problem_dir}/

Begin your investigation now. Use the tools actively."""

    return prompt


def main():
    """Generate and print prompt for a random open problem."""
    problems = load_open_problems()
    if not problems:
        print("Error: No open problems found", file=sys.stderr)
        sys.exit(1)

    # Filter out already-solved problems
    unsolved_problems = []
    for p in problems:
        problem_num = p.get('problem_number', 'unknown')
        solved, _ = is_problem_solved(problem_num)
        if not solved:
            unsolved_problems.append(p)

    if not unsolved_problems:
        print("All open problems have already been attempted!", file=sys.stderr)
        print(f"Total problems: {len(problems)}, all have solution artifacts.", file=sys.stderr)
        sys.exit(0)

    problem = random.choice(unsolved_problems)
    problem_num = problem.get('problem_number', 'unknown')

    # Double-check (in case of race condition or manual file creation)
    solved, artifact_path = is_problem_solved(problem_num)
    if solved:
        print(f"ALREADY_SOLVED:{artifact_path}", file=sys.stdout)
        sys.exit(0)

    prompt = generate_prompt(problem)
    print(prompt)


if __name__ == '__main__':
    main()