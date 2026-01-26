"""Find unformalized problems from all_problems.json."""

import json
import sys
from pathlib import Path

def main():
    import argparse
    parser = argparse.ArgumentParser(description="Find unformalized problems")
    parser.add_argument("n", type=int, help="Number of problems to find")
    parser.add_argument("--list", dest="list_name", default="kourovka",
                       help="Problem list name (default: kourovka)")
    args = parser.parse_args()
    
    n = args.n
    list_name = args.list_name
    
    # Load problems
    problems_file = Path(f"problems/{list_name}/all_problems.json")
    if not problems_file.exists():
        print(f"Error: problems/{list_name}/all_problems.json not found", file=sys.stderr)
        sys.exit(1)
    
    with open(problems_file) as f:
        problems = json.load(f)
    
    # Find unformalized problems
    unformalized = []
    for problem in problems:
        problem_num = problem.get('problem_number')
        if not problem_num:
            continue
        
        # Directory uses problem number: problem_1.3, problem_K-5, etc.
        problem_dir = Path(f"problems/{list_name}/problem_{problem_num}")
        
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