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

    # Check for existing formalization
    formalization_path = Path(problem_dir) / "formalization.lean"
    existing_formalization = None
    if formalization_path.exists():
        existing_formalization = formalization_path.read_text()

    # Get tool documentation
    tool_docs = generate_tool_documentation()

    # Build formalization context
    formalization_context = ""
    if existing_formalization:
        formalization_context = f"""
**IMPORTANT: Existing Formalization Available**

A formalization already exists at {problem_dir}/formalization.lean:

```lean
{existing_formalization}
```

You should BUILD ON THIS FORMALIZATION to complete the proof.
Do not create a new formalization from scratch - extend and complete this one.
"""

    prompt = f"""You are solving Kourovka Notebook problem #{problem_num} (stored as problem_{problem_index}).

**Problem Statement:**
{problem_text}
{formalization_context}
**Your Goal:**
Solve this problem using a systematic, phased approach.

**Output Directory:**
{problem_dir}/

**Systematic Solving Approach:**

Follow these phases in order. Be creative and thorough at each step.

**PHASE 1: Research & Exploration (REQUIRED)**
1. Search web/literature for existing results on this problem
2. Use GAP to test the problem statement on small examples
3. Look for patterns, counterexamples, or special cases
4. Document your findings in comments/notes

**PHASE 2: Proof Strategy (REQUIRED)**
1. Based on Phase 1, create a proof sketch as comments
2. Identify key lemmas you'll need
3. Note which parts seem hardest
4. Be creative - try multiple approaches if first doesn't work

**PHASE 3: Formalization (if attempting proof)**
1. Write the theorem statement in Lean with proper types
2. Break down into lemmas (use 'sorry' initially)
3. Ensure it compiles: {problem_dir}/formalization.lean or {problem_dir}/proof.lean
4. Use Lean 4 skills: /lean4-theorem-proving:build-lean to check compilation

**PHASE 4: Progressive Proof Filling**
1. Fill sorries one at a time, easiest first
2. Use /lean4-theorem-proving:fill-sorry for guidance
3. Try different tactics if stuck
4. Use /lean4-theorem-proving:search-mathlib to find relevant lemmas
5. Be persistent - if one approach fails, try another!

**Five Possible Final Outcomes:**

1. **Found NEW Counterexample:** Write to {problem_dir}/disproof.py (STATUS: NEW_COUNTEREXAMPLE)
2. **Verified PRIOR Result:** Write verification code (STATUS: PRIOR_RESULT_VERIFIED)  
3. **Completed Proof:** Write complete proof to {problem_dir}/proof.lean (STATUS: NEW_PROOF)
4. **Formalized but Unsolved:** Write to {problem_dir}/formalization.lean with sorries (STATUS: FORMALIZED_UNSOLVED)
5. **Could Not Formalize:** Write to {problem_dir}/formalization_attempt_summary.txt (STATUS: COULD_NOT_FORMALIZE)

**REQUIRED: Always create notes.txt**

You MUST create {problem_dir}/notes.txt with this format:

```
STATUS: <one of: NEW_COUNTEREXAMPLE, NEW_PROOF, PRIOR_RESULT_VERIFIED, FORMALIZED_UNSOLVED, COULD_NOT_FORMALIZE>
CATEGORY: <counterexample|proof|formalization|summary>
REFERENCE: <citation if verifying prior work, otherwise "N/A">

<Your detailed summary of the problem, findings, and approach>
```

{tool_docs}

**Success Criteria:**
- Exactly ONE of: disproof.py, proof.lean, formalization.lean, or formalization_attempt_summary.txt
- notes.txt MUST exist with proper STATUS field  
- Lean files must compile (use /lean4-theorem-proving:build-lean)
- Clear documentation of your approach and attempts

**Key Reminders:**
- BE CREATIVE: Try different approaches if stuck
- BE THOROUGH: Test small cases, search for patterns
- BE PERSISTENT: Don't give up after first failed attempt
- USE TOOLS: Lean 4 skills commands are your friends
- DOCUMENT: Explain what you tried and why in notes.txt

DO NOT EXIT until you have created BOTH an artifact file AND notes.txt in {problem_dir}/

Begin Phase 1 (Research & Exploration) now. Use the tools actively and be creative!"""

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