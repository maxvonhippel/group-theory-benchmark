#!/usr/bin/env python3
"""
Generate a prompt from a random open problem for Claude to solve.
"""

import json
import random
from pathlib import Path


def load_open_problems():
    """Load all open problems."""
    problems_file = Path(__file__).parent.parent / "problems/all_problems.json"
    with open(problems_file) as f:
        data = json.load(f)
    return [p for p in data if not p.get('answer')]


def generate_prompt(problem):
    """Generate a solving prompt for Claude."""
    problem_num = problem.get('number', 'unknown')
    problem_text = problem.get('problem', 'No problem text')
    
    prompt = f"""You are solving Kourovka Notebook problem #{problem_num}.

**Problem Statement:**
{problem_text}

**Your Task:**
Use the available MCP tools (GAP and Lean servers) to attempt to solve this problem. 

**Available tools:**
- GAP tools for computational group theory (query_gap, check_group_property, find_counterexample, etc.)
- Lean tools for formal theorem proving (check_theorem, verify_proof, etc.)

**Approach:**
1. Analyze the problem and determine if it's amenable to computational or formal methods
2. Use GAP to search for counterexamples or gather computational evidence
3. If possible, use Lean to formalize and prove results
4. Report your findings - whether you found a counterexample, proof, or got stuck

Work step-by-step and explain your reasoning. If you get stuck, explain why and what would be needed to proceed.

Begin your investigation now."""

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