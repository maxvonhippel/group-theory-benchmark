"""Find unformalized problems from all_problems.json."""

import json
import sys
from pathlib import Path

def main():
    if len(sys.argv) != 2:
        print("Usage: python find_unformalized.py N", file=sys.stderr)
        sys.exit(1)
    
    try:
        n = int(sys.argv[1])
    except ValueError:
        print(f"Error: N must be an integer, got '{sys.argv[1]}'", file=sys.stderr)
        sys.exit(1)
    
    # Load problems
    problems_file = Path("problems/all_problems.json")
    if not problems_file.exists():
        print("Error: problems/all_problems.json not found", file=sys.stderr)
        sys.exit(1)
    
    with open(problems_file) as f:
        problems = json.load(f)
    
    # Find unformalized problems
    unformalized = []
    for problem in problems:
        problem_num = problem.get('problem_number')
        if not problem_num:
            continue
        
        # Directory uses Kourovka number: problem_1.3, problem_19.110, etc.
        problem_dir = Path(f"problems/problem_{problem_num}")
        
        if not problem_dir.exists():
            continue
        
        # Check if already formalized
        formalization_file = problem_dir / "formalization.lean"
        cannot_formalize_file = problem_dir / "cannot_formalize.txt"
        
        # Skip if already processed
        if formalization_file.exists() or cannot_formalize_file.exists():
            continue
        
        unformalized.append(problem_num)
        
        # Stop when we have enough
        if len(unformalized) >= n:
            break
    
    # Output problem numbers, one per line
    for prob in unformalized:
        print(prob)

if __name__ == "__main__":
    main()