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

    # Load all_problems.json to check for lean_formalization
    all_problems_file = problems_dir / "all_problems.json"
    lean_formalizations = {}
    if all_problems_file.exists():
        import json
        with open(all_problems_file) as f:
            problems = json.load(f)
            for p in problems:
                pnum = str(p.get('problem_number', ''))
                if 'lean_formalization' in p and p['lean_formalization']:
                    lean_formalizations[pnum] = p['lean_formalization']

    # Track all problem numbers we've seen
    seen_problems = set()
    
    # Get all problem directories
    if problems_dir.exists():
        for problem_dir in sorted(problems_dir.iterdir()):
            if not problem_dir.is_dir() or problem_dir.name == "all_problems.json":
                continue

            problem_num = problem_dir.name.replace('problem_', '')
            seen_problems.add(problem_num)
            
            solution_info = {
                'number': problem_num,
                'disproof': None,
                'proof': None,
                'formalization': None,
                'lean_formalization_json': None,
                'attempt_summary': None,
                'review': None,
                'notes': None,
                'status': None,
                'reference': None
            }

        # Check for solution artifacts
        disproof_file = problem_dir / "disproof.py"
        proof_file = problem_dir / "proof.lean"
        formalization_file = problem_dir / "problem.lean"
        attempt_summary_file = problem_dir / "formalization_attempt_summary.txt"
        review_file = problem_dir / "review.txt"
        notes_file = problem_dir / "notes.txt"

        if disproof_file.exists():
            solution_info['disproof'] = 'disproof.py'
        if proof_file.exists():
            solution_info['proof'] = 'proof.lean'
        if formalization_file.exists():
            solution_info['formalization'] = 'problem.lean'
        if attempt_summary_file.exists():
            solution_info['attempt_summary'] = 'formalization_attempt_summary.txt'
        
        # Check for lean_formalization in JSON
        if problem_num in lean_formalizations:
            solution_info['lean_formalization_json'] = True

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
                    solution_info['lean_formalization_json']]):
                solutions.append(solution_info)
    
    # Add problems from JSON that only have lean_formalization (no directory)
    for problem_num, formalization in lean_formalizations.items():
        if problem_num not in seen_problems:
            solution_info = {
                'number': problem_num,
                'disproof': None,
                'proof': None,
                'formalization': None,
                'lean_formalization_json': True,
                'attempt_summary': None,
                'review': None,
                'notes': None,
                'status': None,
                'reference': None
            }
            solutions.append(solution_info)

    return solutions


def get_status_display(sol: dict[str, Any]) -> str:
    """Get display string for solution status."""
    status = sol.get('status')

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
        elif sol['lean_formalization_json']:
            artifact = "Lean formalization (JSON)"
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