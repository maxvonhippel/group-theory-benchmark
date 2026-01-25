#!/usr/bin/env python3
"""
Generate README.md with automated solution tracking table.
"""
from pathlib import Path
from typing import Any


# Status values for notes.txt STATUS field
STATUS_NEW_COUNTEREXAMPLE = "NEW_COUNTEREXAMPLE"
STATUS_NEW_PROOF = "NEW_PROOF"
STATUS_PRIOR_RESULT_VERIFIED = "PRIOR_RESULT_VERIFIED"
STATUS_FORMALIZED_UNSOLVED = "FORMALIZED_UNSOLVED"
STATUS_COULD_NOT_FORMALIZE = "COULD_NOT_FORMALIZE"


def parse_notes_file(notes_path: Path) -> dict[str, Any]:
    """Parse notes.txt file for metadata."""
    info: dict[str, str | None] = {
        'status': None,
        'category': None,
        'reference': None,
        'summary': None
    }

    if not notes_path.exists():
        return info

    content = notes_path.read_text()
    lines = content.split('\n')

    for line in lines:
        if line.startswith('STATUS:'):
            info['status'] = line.split(':', 1)[1].strip()
        elif line.startswith('CATEGORY:'):
            info['category'] = line.split(':', 1)[1].strip()
        elif line.startswith('REFERENCE:'):
            info['reference'] = line.split(':', 1)[1].strip()

    return info


def scan_problem_solutions() -> list[dict[str, Any]]:
    """Scan problems/ directory for solution artifacts."""
    problems_dir = Path(__file__).parent.parent / "problems"
    solutions: list[dict[str, Any]] = []

    # Get all problem directories
    if not problems_dir.exists():
        return solutions
    
    # Load all_problems.json to get problem numbers and formalization_status
    import json
    all_problems_file = problems_dir / "all_problems.json"
    problem_index_to_number = {}
    formalization_status_map = {}
    if all_problems_file.exists():
        try:
            with open(all_problems_file) as f:
                all_problems = json.load(f)
                for i, problem in enumerate(all_problems):
                    dir_index = str(i + 1)
                    actual_problem_num = str(problem.get('problem_number', dir_index))
                    # Normalize problem numbers: replace underscores with dots
                    actual_problem_num = actual_problem_num.replace('_', '.')
                    problem_index_to_number[dir_index] = actual_problem_num
                    formalization_status_map[dir_index] = {
                        'status': problem.get('formalization_status'),
                        'reason': problem.get('formalization_reason')
                    }
        except Exception:
            pass

    for problem_dir in sorted(problems_dir.iterdir()):
        if not problem_dir.is_dir() or problem_dir.name == "all_problems.json":
            continue

        dir_name = problem_dir.name.replace('problem_', '')
        
        # Two cases:
        # 1. Directory name contains underscore/period (e.g., "1_20" or "1.20") - it's the actual problem number
        # 2. Directory name is pure number (e.g., "1", "27") - it's an index, look up actual number in JSON
        if '_' in dir_name or '.' in dir_name:
            # Already a problem number, just normalize
            problem_num = dir_name.replace('_', '.')
            dir_index = None  # No index mapping
        else:
            # It's an index, look up the actual problem number
            dir_index = dir_name
            problem_num = problem_index_to_number.get(dir_index, dir_index)
        
        solution_info = {
            'number': problem_num,
            'disproof': None,
            'proof': None,
            'formalization': None,
            'attempt_summary': None,
            'review': None,
            'notes': None,
            'status': None,
            'reference': None,
            'formalization_status': None,
            'formalization_reason': None
        }

        # Check for solution artifacts
        disproof_file = problem_dir / "disproof.py"
        proof_file = problem_dir / "proof.lean"
        formalization_file = problem_dir / "formalization.lean"
        problem_lean_file = problem_dir / "problem.lean"
        cannot_formalize_file = problem_dir / "cannot_formalize.txt"
        attempt_summary_file = problem_dir / "formalization_attempt_summary.txt"
        review_file = problem_dir / "review.txt"
        notes_file = problem_dir / "notes.txt"

        if disproof_file.exists():
            solution_info['disproof'] = 'disproof.py'
        if proof_file.exists():
            solution_info['proof'] = 'proof.lean'
        if formalization_file.exists() or problem_lean_file.exists():
            # Accept either formalization.lean or problem.lean
            solution_info['formalization'] = 'formalization.lean' if formalization_file.exists() else 'problem.lean'
        if cannot_formalize_file.exists():
            solution_info['formalization_status'] = 'cannot_formalize'
            solution_info['formalization_reason'] = cannot_formalize_file.read_text().strip()
        if attempt_summary_file.exists():
            solution_info['attempt_summary'] = 'formalization_attempt_summary.txt'
        
        # Get formalization status from JSON using directory index (if we have one)
        if dir_index and dir_index in formalization_status_map:
            json_status = formalization_status_map[dir_index]
            if json_status['status']:
                solution_info['formalization_status'] = json_status['status']
            if json_status['reason']:
                solution_info['formalization_reason'] = json_status['reason']

        # Parse notes.txt for metadata
        if notes_file.exists():
            solution_info['notes'] = 'notes.txt'
            notes_info = parse_notes_file(notes_file)
            solution_info['status'] = notes_info.get('status')
            solution_info['reference'] = notes_info.get('reference')

        # Check for human review
        if review_file.exists():
            review_text = review_file.read_text().strip()
            if len(review_text) > 10:
                solution_info['review'] = review_text[:10].strip() + "..."
            else:
                solution_info['review'] = review_text

        # Only include if there's at least one artifact
        if any([solution_info['disproof'], solution_info['proof'],
                solution_info['formalization'], solution_info['attempt_summary'],
                solution_info['formalization_status']]):
            solutions.append(solution_info)

    return solutions


def get_status_display(sol: dict[str, Any]) -> str:
    """Get display string for solution status."""
    status = sol.get('status')
    formalization_status = sol.get('formalization_status')

    # Check formalization_status first
    if formalization_status == 'formalized':
        return "Formalized (unsolved)"
    elif formalization_status == 'cannot_formalize':
        return "Cannot formalize"

    if status == STATUS_NEW_COUNTEREXAMPLE:
        return "NEW counterexample"
    elif status == STATUS_NEW_PROOF:
        return "NEW proof"
    elif status == STATUS_PRIOR_RESULT_VERIFIED:
        return "Prior result verified"
    elif status == STATUS_FORMALIZED_UNSOLVED:
        return "Formalized (unsolved)"
    elif status == STATUS_COULD_NOT_FORMALIZE:
        return "Could not formalize"
    else:
        # Infer from artifacts if no explicit status
        if sol['disproof']:
            return "Counterexample (unverified)"
        elif sol['proof']:
            return "Proof (unverified)"
        elif sol['formalization']:
            return "Formalized (unsolved)"
        elif sol['attempt_summary']:
            return "Could not formalize"
        return "Unknown"


def generate_solution_table(solutions: list[dict[str, Any]]) -> str:
    """Generate markdown table for solutions."""
    if not solutions:
        return ""

    table = "\n## AI-Generated Solutions\n\n"
    table += "**Warning**: "
    table += "[No AI-generated proof should be trusted without human review, no matter how formal.]"
    table += "(https://www.lesswrong.com/posts/rhAPh3YzhPoBNpgHg/lies-damned-lies-and-proofs-formal-methods-are-not-slopless)\n\n"

    table += "| Problem | Artifact | Status | Human Review |\n"
    table += "|---------|----------|--------|-------------|\n"

    for sol in solutions:
        # Determine artifact type
        if sol['disproof']:
            artifact = f"`{sol['disproof']}`"
        elif sol['proof']:
            artifact = f"`{sol['proof']}`"
        elif sol['formalization']:
            artifact = f"`{sol['formalization']}`"
        elif sol['attempt_summary']:
            artifact = f"`{sol['attempt_summary']}`"
        else:
            artifact = "N/A"

        # Get status display
        status = get_status_display(sol)

        # Human review status
        if sol['review']:
            review = sol['review']
        else:
            review = "Pending"

        table += f"| {sol['number']} | {artifact} | {status} | {review} |\n"

    return table


def generate_readme() -> str:
    """Generate complete README.md content."""
    
    # Read existing README sections (if any) - for now, start fresh
    readme = "# 🔮 BuddenBench: a Benchmark of Open Nontrivial Group Theory Problems\n\n"
    readme += "This benchmark, affectionately named [`budden-bench`]"
    readme += "(https://x.com/maxvonhippel/status/2014475901384241286?s=20), "
    readme += "measures the ability of models and agents to autonomously solve open and important problems "
    readme += "in mathematics, specifically group theory. In contrast to other problem sets such as the "
    readme += "[Erdős Problems](https://www.erdosproblems.com/), this benchmark is intended to exclusively contain "
    readme += "problems which are of ongoing research interest to working mathematicians.\n\n"
    
    readme += "## Inspiration\n\n"
    readme += "This project was inspired by the paper [Disproof of the Mertens Conjecture]"
    readme += "(https://www.sciencedirect.com/science/article/pii/0022314X85900764) which showed how "
    readme += "computational algebra systems like GAP can be used to solve longstanding mathematical conjectures "
    readme += "by finding counterexamples.\n\n"
    
    readme += "## Tools\n\n"
    readme += "- **[GAP (Groups, Algorithms, Programming)](https://www.gap-system.org/)**: "
    readme += "A system for computational discrete algebra, especially computational group theory\n"
    readme += "- **[Lean 4](https://lean-lang.org/)**: An interactive theorem prover for "
    readme += "formalizing and verifying mathematical proofs\n\n"
    
    # Add solution table
    solutions = scan_problem_solutions()
    if solutions:
        readme += generate_solution_table(solutions)
        readme += "\n"
    
    readme += "## Setup\n\n"
    readme += "```bash\n"
    readme += "make setup  # Install dependencies, build GAP, setup Lean\n"
    readme += "```\n\n"
    
    readme += "## Usage\n\n"
    readme += "```bash\n"
    readme += "make watch-solve  # Launch Claude to solve a random problem\n"
    readme += "make test         # Run test suite\n"
    readme += "```\n\n"
    
    readme += "## Problem Set\n\n"
    readme += "Problems are drawn from the [Kourovka Notebook]"
    readme += "(https://kourovka-notebook.org/), "
    readme += "a collection of unsolved problems in group theory.\n"
    
    return readme


def main() -> None:
    """Generate and write README.md."""
    readme_content = generate_readme()
    
    project_root = Path(__file__).parent.parent
    readme_path = project_root / "README.md"
    
    readme_path.write_text(readme_content)
    print(f"Generated {readme_path}")


if __name__ == '__main__':
    main()