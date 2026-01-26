#!/usr/bin/env python3
"""Create problem directories for Green problems from extracted JSON."""
import json
from pathlib import Path

def main():
    # Load extracted problems
    with open('problems/green/extracted_problems.json') as f:
        problems = json.load(f)
    
    print(f"Creating directories for {len(problems)} Green problems...")
    
    for problem in problems:
        problem_num = problem['problem_number']
        problem_dir = Path(f'problems/green/problem_{problem_num}')
        problem_dir.mkdir(parents=True, exist_ok=True)
        
        # Write problem.json
        with open(problem_dir / 'problem.json', 'w') as f:
            json.dump(problem, f, indent=2, ensure_ascii=False)
    
    print(f"Created {len(problems)} problem directories in problems/green/")

if __name__ == '__main__':
    main()