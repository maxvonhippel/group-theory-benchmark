#!/usr/bin/env python3
"""
Find problems that don't have solution artifacts yet.
"""

import json
import sys
from pathlib import Path


# Solution artifact files - if any exists, problem is considered solved
SOLUTION_ARTIFACTS = [
    'disproof.py',
    'proof.lean',
    'formalization.lean',
    'problem.lean',
    'formalization_attempt_summary.txt',
]


def is_problem_solved(problem_index):
    """Check if a problem already has a solution artifact.
    
    Args:
        problem_index: 1-based index into all_problems.json

    Returns:
        True if solved, False otherwise
    """
    problem_dir = Path(f"problems/problem_{problem_index}")
    for artifact in SOLUTION_ARTIFACTS:
        artifact_path = problem_dir / artifact
        if artifact_path.exists():
            return True
    return False


def find_unsolved_problems(max_count=None):
    """Find open problems without solution artifacts.
    
    Args:
        max_count: Maximum number to return (None for all)
        
    Returns:
        List of (problem_index, problem_number) tuples
    """
    problems_file = Path(__file__).parent.parent / "problems/all_problems.json"
    if not problems_file.exists():
        return []
    
    with open(problems_file) as f:
        all_problems = json.load(f)
    
    unsolved = []
    for i, problem in enumerate(all_problems):
        # Skip problems with answers (closed problems)
        if problem.get('answer'):
            continue
            
        # Skip if already has solution artifact
        if is_problem_solved(i + 1):
            continue
        
        problem_num = problem.get('problem_number', f'{i+1}')
        problem_index = i + 1
        unsolved.append((problem_index, str(problem_num)))
        
        if max_count and len(unsolved) >= max_count:
            break
    
    return unsolved


def main():
    if len(sys.argv) < 2:
        print("Usage: python make/find_unsolved.py [COUNT]")
        sys.exit(1)
    
    count = int(sys.argv[1]) if sys.argv[1] != "all" else None
    problems = find_unsolved_problems(count)
    
    # Print problem_index for shell processing
    for problem_index, problem_num in problems:
        print(problem_index)


if __name__ == '__main__':
    main()