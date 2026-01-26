"""Formalize Kourovka problems in Lean."""

import json
import sys
import subprocess
import tempfile
from pathlib import Path

def load_problems(list_name="kourovka"):
    """Load all problems from JSON for a specific problem list."""
    problems_file = Path(f"problems/{list_name}/all_problems.json")
    if not problems_file.exists():
        print(f"Error: problems/{list_name}/all_problems.json not found")
        sys.exit(1)
    
    with open(problems_file) as f:
        return json.load(f)

def save_problems(problems, list_name="kourovka"):
    """Save problems back to JSON for a specific problem list."""
    problems_file = Path(f"problems/{list_name}/all_problems.json")
    with open(problems_file, 'w') as f:
        json.dump(problems, f, indent=2)

def find_problem(problems, problem_num):
    """Find a specific problem by number."""
    for problem in problems:
        if str(problem.get('problem_number')) == str(problem_num):
            return problem
    return None

def generate_formalization_prompt(problem, problem_dir):
    """Generate prompt for Claude to formalize the problem."""
    problem_num = problem.get('problem_number', 'unknown')
    problem_text = problem.get('problem_text', 'No problem text')
    
    prompt = f"""You are formalizing problem #{problem_num} in Lean 4.

**IMPORTANT: Working Directory**
You are working in: {problem_dir.absolute()}
All files MUST be created in this directory.

**Problem Statement:**
{problem_text}

**Your Goal:**
Create a PERFECT formalization of this problem in Lean 4 with sorry's for unsolved parts.

**Critical Requirements:**
1. The Lean code MUST compile without errors
2. All definitions, types, and statements must be formally correct
3. Use 'sorry' for proof obligations (we're formalizing, not proving)
4. The formalization must EXACTLY capture the problem statement
5. If the problem is vague or unclear, explain why you cannot formalize it

**Success Criteria:**
- Write Lean code to: formalization.lean
- Code must pass: lean formalization.lean (exit code 0)
- No compilation errors allowed
- Must be complete and accurate representation of the problem

**If You Cannot Formalize:**
Some problems cannot be properly formalized because they are:
- Too vague or ambiguous
- Open-ended (e.g., "classify all groups with property X")
- Meta-mathematical questions about decidability/computability
- Asking for examples/constructions rather than statements
- Using concepts not expressible in current Lean/Mathlib
- Missing critical context or definitions

If you determine the problem CANNOT be properly formalized:
1. Create a file: cannot_formalize.txt
2. Write a clear explanation of why (2-3 sentences)
3. DO NOT create formalization.lean
4. Run: bash -c 'kill -9 $PPID' to force exit

**Workflow:**
1. Analyze the problem statement carefully
2. Determine if it CAN be formalized as a precise mathematical statement
3. If NO: Write cannot_formalize.txt, then run: bash -c 'kill -9 $PPID'
4. If YES: Write the Lean formalization
5. Test it with lean CLI
6. If it compiles perfectly: Run: bash -c 'kill -9 $PPID' to force exit
7. If it doesn't compile: Write cannot_formalize.txt, then run: bash -c 'kill -9 $PPID'

**IMPORTANT:**
- DO NOT submit imperfect formalizations
- ALWAYS run bash -c 'kill -9 $PPID' when you finish your task
- If you determine it cannot be formalized, ACCEPT that decision
- Only output code that compiles perfectly OR explain why formalization is impossible

Begin your formalization now."""
    
    return prompt

def validate_lean_file(lean_file, problem_dir):
    """Validate a Lean file compiles correctly using lake.
    
    Args:
        lean_file: Path to the formalization.lean file to validate
        problem_dir: Path to the problem directory for the formalization
    """
    # Copy file to formalization project
    formalization_lib_dir = Path("formalization/Formalization")
    target_file = formalization_lib_dir / "Problem.lean"
    
    import shutil
    shutil.copy(lean_file, target_file)
    
    try:
        result = subprocess.run(
            ['lake', 'build', 'Formalization.Problem'],
            cwd="formalization",
            capture_output=True,
            text=True,
            timeout=600  # 10 minutes for first Mathlib build, much faster after caching
        )
        success = result.returncode == 0
        
        # Clean up
        target_file.unlink(missing_ok=True)
        
        return success, result.stdout, result.stderr
    except subprocess.TimeoutExpired:
        target_file.unlink(missing_ok=True)
        return False, "", "Lean compilation timed out"
    except FileNotFoundError:
        target_file.unlink(missing_ok=True)
        return False, "", "Lake not found. Run 'make setup' first."

def run_claude_formalization(prompt, problem_dir):
    """Run Claude to generate formalization.
    
    Args:
        prompt: The formalization prompt text
        problem_dir: Path to the problem directory where outputs should be created
    """
    prompt_file = Path("/tmp/formalize_prompt.txt")
    prompt_file.write_text(prompt)
    
    # Get absolute paths for MCP config (since we'll change directory)
    project_root = Path.cwd()
    gap_root = project_root / "gap"
    lean_workspace = project_root / "lean_scratch"
    
    mcp_config_file = Path("/tmp/claude_mcp_config.json")
    mcp_config = {
        "mcpServers": {
            "gap": {
                "command": "uv",
                "args": ["run", "gap-mcp"],
                "env": {
                    "GAP_ROOT": str(gap_root)
                }
            },
            "lean": {
                "command": "uv",
                "args": ["--directory", str(project_root), "run", "lean-lsp-mcp"],
                "env": {
                    "LEAN_WORKSPACE": str(lean_workspace)
                }
            }
        }
    }
    mcp_config_file.write_text(json.dumps(mcp_config, indent=2))
    
    print("Launching Claude to formalize problem...")
    print("=" * 60)
    
    try:
        # Run Claude from within the problem directory
        # This way "formalization.lean" is created in the correct location
        result = subprocess.run(
            [
                'claude',
                '--model', 'opus',
                '--mcp-config', str(mcp_config_file),
                '--dangerously-skip-permissions'
            ],
            stdin=open(prompt_file),
            capture_output=False,  # Let output stream
            text=True,
            timeout=600,  # 10 minutes for Mathlib builds
            cwd=str(problem_dir)  # Run from problem directory
        )
        
        # Check for output files in problem directory
        # This handles cases where kill -9 terminates the process with signal exit code
        # but the formalization was completed successfully before termination
        lean_file = problem_dir / "formalization.lean"
        cannot_file = problem_dir / "cannot_formalize.txt"
        
        if lean_file.exists() or cannot_file.exists():
            return True  # Task completed successfully (output files exist)
        
        # No output files exist - check if normal exit
        if result.returncode == 0:
            return False  # Normal exit but no outputs = failure
        
        return False  # Process failed without producing output
    except subprocess.TimeoutExpired:
        print("\nError: Claude formalization timed out")
        return False
    except KeyboardInterrupt:
        print("\nFormalization interrupted by user")
        return False

def get_problem_dir(problem_num, list_name="kourovka"):
    """Get problem directory path for a given problem number in a specific list."""
    # Directory uses problem number directly: problem_1.3, problem_K-5, etc.
    return Path(f"problems/{list_name}/problem_{problem_num}")


def main():
    import argparse
    parser = argparse.ArgumentParser(description="Formalize a problem using Claude")
    parser.add_argument("problem_num", help="Problem number to formalize")
    parser.add_argument("--list", dest="list_name", default="kourovka", 
                       help="Problem list name (default: kourovka)")
    args = parser.parse_args()
    
    problem_num = args.problem_num
    list_name = args.list_name
    
    # Load problems
    problems = load_problems(list_name)
    problem = find_problem(problems, problem_num)
    
    if not problem:
        print(f"Error: Problem #{problem_num} not found in all_problems.json")
        sys.exit(1)
    
    # Get problem directory
    problem_dir = get_problem_dir(problem_num, list_name)
    if not problem_dir:
        print(f"Error: Could not determine directory for problem #{problem_num} in list '{list_name}'")
        sys.exit(1)
    
    # Create problem directory if it doesn't exist
    problem_dir.mkdir(parents=True, exist_ok=True)
    
    # Check if already processed (formalized OR determined unformalizable)
    formalization_file = problem_dir / "formalization.lean"
    cannot_formalize_file = problem_dir / "cannot_formalize.txt"
    
    if formalization_file.exists():
        print(f"✓ Problem #{problem_num} already formalized: {formalization_file}")
        print("Skipping (already complete)")
        sys.exit(0)
    
    if cannot_formalize_file.exists():
        reason = cannot_formalize_file.read_text().strip()
        print(f"✓ Problem #{problem_num} already determined to be unformalizable")
        print(f"\nReason: {reason[:200]}{'...' if len(reason) > 200 else ''}")
        print("\nSkipping (already processed)")
        sys.exit(0)
    
    print(f"Problem #{problem_num}: {problem.get('problem_text', '')[:100]}...")
    print()
    
    # Generate prompt
    prompt = generate_formalization_prompt(problem, problem_dir)
    
    # Run Claude from problem directory
    success = run_claude_formalization(prompt, problem_dir)
    
    if not success:
        print("\nClaude formalization process failed or was interrupted.")
        sys.exit(1)
    
    # Check for formalization.lean or cannot_formalize.txt in problem directory
    lean_file = problem_dir / "formalization.lean"
    cannot_formalize_file = problem_dir / "cannot_formalize.txt"
    
    if cannot_formalize_file.exists():
        reason = cannot_formalize_file.read_text().strip()
        print("\n" + "=" * 60)
        print(f"Problem #{problem_num} CANNOT be formalized")
        print(f"Reason: {reason}")
        print("=" * 60)
        
        # Update JSON to mark as unformalizable
        problem['formalization_status'] = 'cannot_formalize'
        problem['formalization_reason'] = reason
        save_problems(problems, list_name)
        
        sys.exit(0)  # Not an error - just can't be formalized
    
    if not lean_file.exists():
        print("\nError: Neither formalization.lean nor cannot_formalize.txt was created.")
        print("Claude may have failed to complete the task.")
        sys.exit(1)
    
    # Validate the Lean code
    print("\n" + "=" * 60)
    print("Validating Lean formalization...")
    valid, stdout, stderr = validate_lean_file(lean_file, problem_dir)
    
    if not valid:
        print("\nValidation FAILED. Lean code does not compile perfectly.")
        print("\nStdout:", stdout)
        print("\nStderr:", stderr)
        print("\nCannot save imperfect formalization.")
        lean_file.unlink()  # Clean up
        sys.exit(1)
    
    # File is already in problem directory (no need to move)
    print(f"Formalization saved to: {lean_file}")
    
    # Update JSON to mark as successfully formalized
    problem['formalization_status'] = 'formalized'
    save_problems(problems, list_name)
    
    print("\n" + "=" * 60)
    print(f"SUCCESS: Problem #{problem_num} formalized")
    print(f"Saved to: {formalization_file}")
    print(f"Formalization: {formalization_file.stat().st_size} bytes")
    print("=" * 60)

if __name__ == "__main__":
    main()