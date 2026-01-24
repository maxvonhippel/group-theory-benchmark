"""Formalize Kourovka problems in Lean."""

import json
import sys
import subprocess
import tempfile
from pathlib import Path

def load_problems():
    """Load all problems from JSON."""
    problems_file = Path("problems/all_problems.json")
    if not problems_file.exists():
        print("Error: problems/all_problems.json not found")
        sys.exit(1)
    
    with open(problems_file) as f:
        return json.load(f)

def save_problems(problems):
    """Save problems back to JSON."""
    problems_file = Path("problems/all_problems.json")
    with open(problems_file, 'w') as f:
        json.dump(problems, f, indent=2)

def find_problem(problems, problem_num):
    """Find a specific problem by number."""
    for problem in problems:
        if str(problem.get('problem_number')) == str(problem_num):
            return problem
    return None

def generate_formalization_prompt(problem):
    """Generate prompt for Claude to formalize the problem."""
    problem_num = problem.get('problem_number', 'unknown')
    problem_text = problem.get('problem_text', 'No problem text')
    
    prompt = f"""You are formalizing Kourovka Notebook problem #{problem_num} in Lean 4.

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
Explain clearly why:
- Problem too vague/ambiguous
- Concept not expressible in Lean
- Missing definitions/context
- Other specific reasons

**Workflow:**
1. Analyze the problem statement carefully
2. Write the Lean formalization
3. Test it with lean CLI
4. If it compiles perfectly: SUCCESS
5. If it doesn't compile or is incomplete: Explain why and STOP

DO NOT submit imperfect formalizations.
Only output code that compiles perfectly.

Begin your formalization now."""
    
    return prompt

def validate_lean_file(lean_file):
    """Validate a Lean file compiles correctly using lake."""
    # Move file to formalization project
    formalization_dir = Path("formalization/Formalization")
    formalization_dir.mkdir(parents=True, exist_ok=True)
    target_file = formalization_dir / "Problem.lean"
    
    # Copy to formalization project
    import shutil
    shutil.copy(lean_file, target_file)
    
    try:
        result = subprocess.run(
            ['lake', 'build', 'Formalization.Problem'],
            cwd="formalization",
            capture_output=True,
            text=True,
            timeout=120
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

def run_claude_formalization(prompt):
    """Run Claude to generate formalization."""
    prompt_file = Path("/tmp/formalize_prompt.txt")
    prompt_file.write_text(prompt)
    
    mcp_config_file = Path("/tmp/claude_mcp_config.json")
    mcp_config = {
        "mcpServers": {
            "gap": {
                "command": "uv",
                "args": ["run", "gap-mcp"],
                "env": {
                    "GAP_ROOT": str(Path.cwd() / "gap")
                }
            },
            "lean": {
                "command": "uv",
                "args": ["--directory", str(Path.cwd()), "run", "lean-lsp-mcp"],
                "env": {
                    "LEAN_WORKSPACE": str(Path.cwd() / "lean_scratch")
                }
            }
        }
    }
    mcp_config_file.write_text(json.dumps(mcp_config, indent=2))
    
    print("Launching Claude to formalize problem...")
    print("=" * 60)
    
    try:
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
            timeout=300
        )
        return result.returncode == 0
    except subprocess.TimeoutExpired:
        print("\nError: Claude formalization timed out")
        return False
    except KeyboardInterrupt:
        print("\nFormalization interrupted by user")
        return False

def main():
    if len(sys.argv) != 2:
        print("Usage: python make/formalize_problem.py PROBLEM_NUM")
        sys.exit(1)
    
    problem_num = sys.argv[1]
    
    # Load problems
    problems = load_problems()
    problem = find_problem(problems, problem_num)
    
    if not problem:
        print(f"Error: Problem #{problem_num} not found in all_problems.json")
        sys.exit(1)
    
    # Check if already formalized
    if 'lean_formalization' in problem and problem['lean_formalization']:
        print(f"Problem #{problem_num} already has a Lean formalization.")
        print("Exiting (use --force to override in future)")
        sys.exit(0)
    
    print(f"Problem #{problem_num}: {problem.get('problem_text', '')[:100]}...")
    print()
    
    # Generate prompt
    prompt = generate_formalization_prompt(problem)
    
    # Run Claude
    success = run_claude_formalization(prompt)
    
    if not success:
        print("\nClaude formalization process failed or was interrupted.")
        sys.exit(1)
    
    # Check for formalization.lean in current directory
    lean_file = Path("formalization.lean")
    if not lean_file.exists():
        print("\nError: No formalization.lean file was created.")
        print("Claude may have determined the problem cannot be formalized.")
        sys.exit(1)
    
    # Validate the Lean code
    print("\n" + "=" * 60)
    print("Validating Lean formalization...")
    valid, stdout, stderr = validate_lean_file(lean_file)
    
    if not valid:
        print("\nValidation FAILED. Lean code does not compile perfectly.")
        print("\nStdout:", stdout)
        print("\nStderr:", stderr)
        print("\nCannot add imperfect formalization to JSON.")
        lean_file.unlink()  # Clean up
        sys.exit(1)
    
    # Read the formalization
    lean_code = lean_file.read_text()
    
    # Update problem JSON
    problem['lean_formalization'] = lean_code
    save_problems(problems)
    
    # Clean up
    lean_file.unlink()
    
    print("\n" + "=" * 60)
    print(f"SUCCESS: Problem #{problem_num} formalized and added to JSON")
    print(f"Formalization: {len(lean_code)} characters")
    print("=" * 60)

if __name__ == "__main__":
    main()