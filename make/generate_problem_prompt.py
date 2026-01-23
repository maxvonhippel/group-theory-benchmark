#!/usr/bin/env python3
"""
Generate a prompt from a random open problem for Claude to solve.
"""

import ast
import json
import random
import sys
from pathlib import Path

from typing import Any


# Solution artifact files - if any exists, problem is considered solved
SOLUTION_ARTIFACTS = [
    'disproof.py',
    'proof.lean',
    'problem.lean',
    'formalization_attempt_summary.txt',
]


def get_problem_dir(problem_index: int) -> Path:
    """Get the directory path for a problem by its index.
    
    Args:
        problem_index: 1-based index into all_problems.json
        
    Returns:
        Path to problem_<index> directory
    """
    return Path(__file__).parent.parent / "problems" / f"problem_{problem_index}"


def is_problem_solved(problem_index: int) -> tuple[bool, str | None]:
    """Check if a problem already has a solution artifact.
    
    Args:
        problem_index: 1-based index into all_problems.json

    Returns:
        (is_solved, artifact_path) - True and path if solved, False and None otherwise
    """
    problem_dir = get_problem_dir(problem_index)
    for artifact in SOLUTION_ARTIFACTS:
        artifact_path = problem_dir / artifact
        if artifact_path.exists():
            return True, str(artifact_path)
    return False, None


def load_open_problems() -> list[tuple[int, dict[str, Any]]]:
    """Load all open problems with their indices.
    
    Returns:
        List of tuples: (index, problem_dict) where index is 1-based
    """
    problems_file = Path(__file__).parent.parent / "problems/all_problems.json"
    with open(problems_file) as f:
        data = json.load(f)
    # Return (1-based index, problem) tuples for problems without answers
    return [(i+1, p) for i, p in enumerate(data) if not p.get('answer')]


def extract_gap_tool_docs(mcp_server_path: Path) -> list[str]:
    """Extract tool documentation from the GAP MCP server file using AST."""
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


def generate_tool_documentation() -> str:
    """Generate documentation for all available tools."""
    project_root = Path(__file__).parent.parent

    gap_tools = extract_gap_tool_docs(project_root / "src/tools/gap_mcp_server.py")

    doc = "**Available Tools:**\n\n"

    if gap_tools:
        doc += "GAP MCP Server (computational group theory):\n"
        doc += "\n".join(gap_tools) + "\n\n"

    # Lean 4 skills (Claude Code plugins from cameronfreer/lean4-skills)
    doc += """Lean 4 Skills (theorem proving via Claude Code plugins):
  Commands (use these directly):
  - `/lean4-theorem-proving:build-lean`: Compile Lean project with categorized error analysis
  - `/lean4-theorem-proving:fill-sorry [file:line]`: Interactive guidance for completing proofs
  - `/lean4-theorem-proving:analyze-sorries`: Identify incomplete proofs and categorize by difficulty
  - `/lean4-theorem-proving:check-axioms`: Verify proofs use only standard axioms
  - `/lean4-theorem-proving:search-mathlib`: Find relevant lemmas in mathlib
  - `/lean4-theorem-proving:golf-proofs`: Optimize proof size (use after successful compilation)
  - `/lean4-theorem-proving:clean-warnings`: Address linter warnings systematically
  - `/lean4-theorem-proving:refactor-have`: Extract have-blocks into separate lemmas

  Subagents (for automated proof work):
  - Proof repair agent: Automatically fix broken proofs
  - Sorry filling agent: Complete proofs with sorry placeholders
  - Axiom elimination agent: Remove unnecessary axioms
  - Proof golfing agent: Optimize proof length"""

    return doc


def generate_prompt(problem_index: int, problem: dict[str, Any]) -> str:
    """Generate a solving prompt for Claude.
    
    Args:
        problem_index: 1-based index into all_problems.json
        problem: The problem dictionary
    """
    problem_num = problem.get('problem_number', 'unknown')
    problem_text = problem.get('problem_text', 'No problem text')
    project_root = Path(__file__).parent.parent
    problem_dir = f"problems/problem_{problem_index}"

    # Get tool documentation
    tool_docs = generate_tool_documentation()

    prompt = f"""You are solving Kourovka Notebook problem #{problem_num} (stored as problem_{problem_index}).

**Problem Statement:**
{problem_text}

**Your Goal:**
Determine if this problem can be solved, and produce the appropriate artifact.

**Output Directory:**
{problem_dir}/

**Five Possible Outcomes:**

1. **Found a NEW Counterexample (via GAP)**
   - Write Python/GAP code to: {problem_dir}/disproof.py
   - Must generate and verify a concrete counterexample
   - Include comments explaining why it's a counterexample
   - Use STATUS: NEW_COUNTEREXAMPLE in notes.txt

2. **Verified a PRIOR Counterexample or Result**
   - If you find the problem was already solved in published literature:
   - Write verification code to: {problem_dir}/disproof.py (for counterexamples)
     or {problem_dir}/proof.lean (for proofs)
   - Cite the original source
   - Use STATUS: PRIOR_RESULT_VERIFIED in notes.txt

3. **Proved the Theorem (via Lean)**
   - Write Lean proof to: {problem_dir}/proof.lean
   - Must compile without errors
   - No 'sorry' or 'admit' allowed
   - Use STATUS: NEW_PROOF in notes.txt

4. **Formalized but Unsolved**
   - Write formalization to: {problem_dir}/problem.lean
   - Include definitions, types, and problem statement
   - Use 'sorry' for unsolved parts
   - Add comments explaining what you tried and why it's hard
   - Use STATUS: FORMALIZED_UNSOLVED in notes.txt

5. **Could Not Formalize**
   - Write summary to: {problem_dir}/formalization_attempt_summary.txt
   - Use this when the problem is too open-ended, vague, or requires
     mathematical infrastructure beyond what's available in Lean
   - Explain what aspects made formalization difficult
   - Document any partial progress or insights gained
   - Use STATUS: COULD_NOT_FORMALIZE in notes.txt

**REQUIRED: Always create notes.txt**

You MUST create {problem_dir}/notes.txt with this format:

```
STATUS: <one of: NEW_COUNTEREXAMPLE, NEW_PROOF, PRIOR_RESULT_VERIFIED, FORMALIZED_UNSOLVED, COULD_NOT_FORMALIZE>
CATEGORY: <counterexample|proof|formalization|summary>
REFERENCE: <citation if verifying prior work, otherwise "N/A">

<Your detailed summary of the problem, findings, and approach>
```

{tool_docs}

**Workflow:**
1. Search literature/web for existing results on this problem
2. Use GAP tools to search for counterexamples
3. If no counterexample found, attempt Lean proof
4. If proof is too difficult, provide formalization with sorry
5. If formalization itself is infeasible, write formalization_attempt_summary.txt
6. ALWAYS write notes.txt with your findings

**Success Criteria:**
- Exactly ONE of: disproof.py, proof.lean, problem.lean, or formalization_attempt_summary.txt exists
- notes.txt MUST exist with proper STATUS field
- File compiles/runs without errors (except sorry in problem.lean)
- Clear explanation of your approach in notes.txt

DO NOT EXIT until you have created BOTH an artifact file AND notes.txt in {problem_dir}/

Begin your investigation now. Use the tools actively."""

    return prompt


def main() -> None:
    """Generate and print prompt for a random open problem."""
    problems = load_open_problems()
    if not problems:
        print("Error: No open problems found", file=sys.stderr)
        sys.exit(1)

    # Filter out already-solved problems
    unsolved_problems = []
    for problem_index, problem in problems:
        solved, _ = is_problem_solved(problem_index)
        if not solved:
            unsolved_problems.append((problem_index, problem))

    if not unsolved_problems:
        print("All open problems have already been attempted!", file=sys.stderr)
        print(f"Total problems: {len(problems)}, all have solution artifacts.", file=sys.stderr)
        sys.exit(0)

    problem_index, problem = random.choice(unsolved_problems)

    # Double-check (in case of race condition or manual file creation)
    solved, artifact_path = is_problem_solved(problem_index)
    if solved:
        print(f"ALREADY_SOLVED:{artifact_path}", file=sys.stdout)
        sys.exit(0)

    prompt = generate_prompt(problem_index, problem)
    print(prompt)


if __name__ == '__main__':
    main()