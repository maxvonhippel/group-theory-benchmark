"""Fix duplicate directories after migration - merge underscore versions into dot versions."""

import shutil
from pathlib import Path


def main():
    problems_dir = Path("problems")
    
    # Find all underscore directories
    underscore_dirs = sorted(problems_dir.glob("problem_*_*"))
    
    print(f"Found {len(underscore_dirs)} underscore directories to merge")
    
    fixed = 0
    for underscore_dir in underscore_dirs:
        # Get the corresponding dot directory name
        dir_name = underscore_dir.name.replace('problem_', '')
        dot_name = dir_name.replace('_', '.')
        dot_dir = problems_dir / f"problem_{dot_name}"
        
        # Merge contents
        if dot_dir.exists():
            # Copy all files from underscore to dot (except problem.json which already exists)
            for item in underscore_dir.iterdir():
                if item.name != 'problem.json':
                    target = dot_dir / item.name
                    if item.is_file():
                        shutil.copy2(item, target)
                        print(f"  Copied {item.name} from {underscore_dir.name} to {dot_dir.name}")
            
            # Remove the empty underscore directory
            shutil.rmtree(underscore_dir)
            print(f"  Removed duplicate: {underscore_dir.name}")
            fixed += 1
        else:
            # No dot version exists, just rename the underscore one
            underscore_dir.rename(dot_dir)
            print(f"  Renamed {underscore_dir.name} -> {dot_dir.name}")
            fixed += 1
    
    print(f"\nFixed {fixed} directories")
    return 0


if __name__ == "__main__":
    exit(main())