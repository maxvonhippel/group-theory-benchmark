#!/usr/bin/env python3
"""
Generate README.md with automated solution tracking table.
"""
from pathlib import Path


# Status values for notes.txt STATUS field
STATUS_NEW_COUNTEREXAMPLE = "NEW_COUNTEREXAMPLE"
STATUS_NEW_PROOF = "NEW_PROOF"
STATUS_PRIOR_RESULT_VERIFIED = "PRIOR_RESULT_VERIFIED"
STATUS_FORMALIZED_UNSOLVED = "FORMALIZED_UNSOLVED"
STATUS_COULD_NOT_FORMALIZE = "COULD_NOT_FORMALIZE"


def parse_notes_file(notes_path: Path) -> dict:
    """Parse notes.txt file for metadata."""
    info = {
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


def scan_problem_solutions():
    """Scan problems/ directory for solution artifacts."""
    problems_dir = Path(__file__).parent.parent / "problems"
    solutions = []

    # Get all problem directories
    if not problems_dir.exists():
        return solutions

    for problem_dir in sorted(problems_dir.iterdir()):
        if not problem_dir.is_dir() or problem_dir.name == "all_problems.json":
            continue

        problem_num = problem_dir.name
        solution_info = {
            'number': problem_num,
            'disproof': None,
            'proof': None,
            'formalization': None,
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
                solution_info['formalization'], solution_info['attempt_summary']]):
            solutions.append(solution_info)

    return solutions


def get_status_display(sol: dict) -> str:
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


def generate_solution_table(solutions):
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


def generate_readme():
    """Generate complete README.md content."""
    
    # Read existing README sections (if any) - for now, start fresh
    readme = "# Group Theory Benchmark\n\n"
    readme += "An AI agent benchmark for solving abstract algebra problems using GAP "
    readme += "and Lean 4.\n\n"
    
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


def main():
    """Generate and write README.md."""
    readme_content = generate_readme()
    
    project_root = Path(__file__).parent.parent
    readme_path = project_root / "README.md"
    
    readme_path.write_text(readme_content)
    print(f"Generated {readme_path}")


if __name__ == '__main__':
    main()