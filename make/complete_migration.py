"""Complete migration of all problem directories to Kourovka numbering convention.

This fixes the incomplete migration by handling ALL directories.
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
    
    # Load problems to build index -> problem_number mapping
    with open(all_problems_file) as f:
        problems = json.load(f)
    
    # Build mapping: index (1-based) -> problem_number
    index_to_number = {}
    for i, problem in enumerate(problems):
        index_to_number[i + 1] = str(problem.get('problem_number', f'{i+1}'))
    
    # Find ALL directories still using sequential numbering (problem_N where N is just digits)
    unmigrated = []
    for item in problems_dir.iterdir():
        if not item.is_dir():
            continue
        
        # Check if it's problem_DIGITS (no dots)
        if item.name.startswith('problem_'):
            suffix = item.name.replace('problem_', '')
            # If suffix is purely numeric (no dots), it needs migration
            if suffix.isdigit():
                old_index = int(suffix)
                if old_index in index_to_number:
                    problem_num = index_to_number[old_index]
                    new_dir_name = f"problem_{problem_num}"
                    new_dir = problems_dir / new_dir_name
                    unmigrated.append((item, new_dir, old_index, problem_num))
    
    print(f"Found {len(unmigrated)} unmigrated directories")
    
    if not unmigrated:
        print("All directories already migrated!")
        return 0
    
    # Show sample
    print("\nSample migrations:")
    for old_dir, new_dir, old_idx, num in unmigrated[:10]:
        print(f"  {old_dir.name} → {new_dir.name}")
    if len(unmigrated) > 10:
        print(f"  ... and {len(unmigrated) - 10} more")
    
    # Execute migrations
    print("\nExecuting migrations...")
    migrated_count = 0
    skipped_count = 0
    
    for old_dir, new_dir, old_idx, problem_num in unmigrated:
        if new_dir.exists():
            # Target exists - need to merge
            print(f"  Merging {old_dir.name} → {new_dir.name} (target exists)")
            # Copy all files except problem.json (which should be the same)
            for item in old_dir.iterdir():
                if item.name != 'problem.json':
                    target = new_dir / item.name
                    if item.is_file() and not target.exists():
                        shutil.copy2(item, target)
            shutil.rmtree(old_dir)
            migrated_count += 1
        else:
            # Simple rename
            print(f"  {old_dir.name} → {new_dir.name}")
            old_dir.rename(new_dir)
            migrated_count += 1
    
    print(f"\nMigration complete:")
    print(f"  Migrated: {migrated_count}")
    print(f"  Skipped: {skipped_count}")
    
    # Verify no sequential directories remain
    remaining = []
    for item in problems_dir.iterdir():
        if item.is_dir() and item.name.startswith('problem_'):
            suffix = item.name.replace('problem_', '')
            if suffix.isdigit():
                remaining.append(item.name)
    
    if remaining:
        print(f"\nWarning: {len(remaining)} sequential directories still remain:")
        for name in remaining[:5]:
            print(f"  {name}")
    else:
        print("\nVerification: All directories now use Kourovka convention!")
    
    return 0


if __name__ == "__main__":
    exit(main())