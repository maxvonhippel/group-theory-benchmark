"""Migrate problem directories to Kourovka numbering convention.

Renames all directories from problem_N to problem_X.Y format.
"""

import json
import shutil
from pathlib import Path


def main():
    problems_dir = Path("problems")
    all_problems_file = problems_dir / "all_problems.json"
    
    if not all_problems_file.exists():
        print(f"Error: {all_problems_file} not found")
        return 1
    
    # Load problems
    with open(all_problems_file) as f:
        problems = json.load(f)
    
    # Build rename map
    renames = []
    for i, problem in enumerate(problems):
        old_dir_name = f"problem_{i + 1}"
        old_dir = problems_dir / old_dir_name
        
        if not old_dir.exists():
            # Check if it's already in underscore format
            problem_num = str(problem.get('problem_number', f'{i+1}'))
            old_dir_name = f"problem_{problem_num.replace('.', '_')}"
            old_dir = problems_dir / old_dir_name
            
            if not old_dir.exists():
                print(f"Warning: Directory not found for problem {i+1}: {old_dir}")
                continue
        
        # Get new name using Kourovka number
        problem_num = str(problem.get('problem_number', f'{i+1}'))
        new_dir_name = f"problem_{problem_num}"
        new_dir = problems_dir / new_dir_name
        
        if old_dir != new_dir:
            renames.append((old_dir, new_dir, problem_num))
    
    # Show plan
    print(f"Will rename {len(renames)} directories:")
    for old, new, num in renames[:10]:
        print(f"  {old.name} → {new.name}")
    if len(renames) > 10:
        print(f"  ... and {len(renames) - 10} more")
    
    # Execute renames
    print("\nExecuting renames...")
    for old_dir, new_dir, problem_num in renames:
        if new_dir.exists():
            print(f"Error: Target already exists: {new_dir}")
            continue
        
        print(f"  {old_dir.name} → {new_dir.name}")
        old_dir.rename(new_dir)
    
    print(f"\nMigration complete: renamed {len(renames)} directories")
    return 0


if __name__ == "__main__":
    exit(main())