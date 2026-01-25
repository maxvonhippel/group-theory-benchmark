#!/usr/bin/env python3
"""
Find problems that don't have formalization.lean yet.
"""

import json
import sys
from pathlib import Path


def find_unformalized_problems(max_count=None):
    """Find problems without formalization.lean.
    
    Args:
        max_count: Maximum number to return (None for all)
        
    Returns:
        List of problem numbers (as strings)
    """
    problems_file = Path(__file__).parent.parent / "problems/all_problems.json"
    if not problems_file.exists():
        return []
    
    with open(problems_file) as f:
        all_problems = json.load(f)
    
    unformalized = []
    for i, problem in enumerate(all_problems):
        problem_dir = Path(f"problems/problem_{i+1}")
        formalization_file = problem_dir / "formalization.lean"
        
        if not formalization_file.exists():
            problem_num = problem.get('problem_number', f'{i+1}')
            unformalized.append(str(problem_num))
            
            if max_count and len(unformalized) >= max_count:
                break
    
    return unformalized


def main():
    if len(sys.argv) < 2:
        print("Usage: python make/find_unformalized.py [COUNT]")
        sys.exit(1)
    
    count = int(sys.argv[1]) if sys.argv[1] != "all" else None
    problems = find_unformalized_problems(count)
    
    # Print one per line for easy shell processing
    for p in problems:
        print(p)


if __name__ == '__main__':
    main()