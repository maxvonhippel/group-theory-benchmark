#!/usr/bin/env python3
"""
Validate a Lean solution file.
Checks that:
1. The file exists
2. It compiles without errors
3. It contains no 'sorry' or 'admit'
4. It contains an actual proof (not just axioms)
"""

import re
import subprocess
import sys
from pathlib import Path


def validate_solution(solution_path: Path) -> tuple[bool, str]:
    """Validate a Lean solution file. Returns (success, message)."""
    
    if not solution_path.exists():
        return False, f"Solution file not found: {solution_path}"
    
    # Read the file
    content = solution_path.read_text()
    
    # Check for sorry/admit
    if re.search(r'\bsorry\b', content, re.IGNORECASE):
        return False, "Solution contains 'sorry' - incomplete proof"
    
    if re.search(r'\badmit\b', content, re.IGNORECASE):
        return False, "Solution contains 'admit' - incomplete proof"
    
    # Check it actually contains theorem/lemma/def
    if not re.search(r'\b(theorem|lemma|def)\b', content):
        return False, "Solution contains no theorem, lemma, or definition"
    
    # Try to compile with Lean using lake build
    # Solutions are in scratch/solutions which should be a Lean project
    try:
        # Get the module name from the filename
        module_name = solution_path.stem
        
        result = subprocess.run(
            ["lake", "build", module_name],
            capture_output=True,
            text=True,
            timeout=60,
            cwd=solution_path.parent
        )
        
        if result.returncode != 0:
            return False, f"Lean compilation failed:\n{result.stderr}\n{result.stdout}"
        
        return True, "Solution validated successfully"
        
    except subprocess.TimeoutExpired:
        return False, "Lean compilation timed out after 60 seconds"
    except FileNotFoundError:
        return False, "Lean compiler not found - is Lean installed?"
    except Exception as e:
        return False, f"Error during validation: {e}"


def main():
    if len(sys.argv) != 2:
        print("Usage: uv run python make/validate_lean_solution.py <solution_file>")
        sys.exit(1)
    
    solution_path = Path(sys.argv[1])
    success, message = validate_solution(solution_path)
    
    print(message)
    sys.exit(0 if success else 1)


if __name__ == "__main__":
    main()