"""
Generate README.md with automated solution tracking table.
"""
from pathlib import Path
from typing import Any, Optional


# Status values for notes.txt STATUS field
STATUS_NEW_COUNTEREXAMPLE = "NEW_COUNTEREXAMPLE"
STATUS_NEW_PROOF = "NEW_PROOF"
STATUS_PRIOR_RESULT_VERIFIED = "PRIOR_RESULT_VERIFIED"
STATUS_FORMALIZED_UNSOLVED = "FORMALIZED_UNSOLVED"
STATUS_COULD_NOT_FORMALIZE = "COULD_NOT_FORMALIZE"


def parse_notes_file(notes_path: Path) -> dict[str, Any]:
    """Parse notes.txt file for metadata."""
    info: dict[str, Optional[str]] = {
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


def scan_problem_solutions(list_name: Optional[str] = None) -> list[dict[str, Any]]:
    """Scan problems/ directory for solution artifacts.
    
    Args:
        list_name: Specific problem list to scan (e.g., 'kourovka', 'klee'), or None for all lists
    """
    import json
    problems_base_dir = Path(__file__).parent.parent / "problems"
    solutions: list[dict[str, Any]] = []

    if not problems_base_dir.exists():
        return solutions
    
    # Determine which lists to scan
    if list_name:
        list_dirs = [problems_base_dir / list_name]
    else:
        # Scan all subdirectories (each is a problem list)
        list_dirs = [d for d in problems_base_dir.iterdir() if d.is_dir()]
    
    for list_dir in sorted(list_dirs):
        if not list_dir.exists():
            continue
            
        current_list_name = list_dir.name
        
        # Load all_problems.json to get formalization_status
        all_problems_file = list_dir / "all_problems.json"
        formalization_status_map = {}
        if all_problems_file.exists():
            try:
                with open(all_problems_file) as f:
                    all_problems = json.load(f)
                    for problem in all_problems:
                        problem_num = str(problem.get('problem_number'))
                        formalization_status_map[problem_num] = {
                            'status': problem.get('formalization_status'),
                            'reason': problem.get('formalization_reason')
                        }
            except Exception as e:
                import sys
                print(f"Warning: Could not load formalization status for {current_list_name}: {e}", file=sys.stderr)

        for problem_dir in sorted(list_dir.iterdir()):
            if not problem_dir.is_dir() or problem_dir.name == "all_problems.json":
                continue

            # All directories now consistently use problem_X.Y format (e.g., problem_1.3, problem_K-5)
            problem_num = problem_dir.name.replace('problem_', '')
            
            solution_info = {
                'number': problem_num,
                'list': current_list_name,
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
            # Prefer cannot_formalize.txt (new format) over formalization_attempt_summary.txt (legacy)
            if cannot_formalize_file.exists():
                solution_info['formalization_status'] = 'cannot_formalize'
                solution_info['formalization_reason'] = cannot_formalize_file.read_text().strip()
                solution_info['artifact'] = 'cannot_formalize.txt'
            elif attempt_summary_file.exists():
                solution_info['formalization_status'] = 'cannot_formalize'
                solution_info['artifact'] = 'formalization_attempt_summary.txt'
            
            # Get formalization status from JSON
            if problem_num in formalization_status_map:
                json_status = formalization_status_map[problem_num]
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


def generate_solution_table(solutions: list[dict[str, Any]], show_list_column: bool = True) -> str:
    """Generate markdown table for solutions."""
    if not solutions:
        return ""

    table = "\n## AI-Generated Solutions\n\n"
    table += "**Warning**: "
    table += "[No AI-generated proof should be trusted without human review, no matter how formal.]"
    table += "(https://www.lesswrong.com/posts/rhAPh3YzhPoBNpgHg/lies-damned-lies-and-proofs-formal-methods-are-not-slopless)\n\n"

    if show_list_column:
        table += "| Problem | List | Artifact | Status | Human Review |\n"
        table += "|---------|------|----------|--------|-------------|\n"
    else:
        table += "| Problem | Artifact | Status | Human Review |\n"
        table += "|---------|----------|--------|-------------|\n"

    for sol in solutions:
        # Determine artifact type and create link to actual file
        artifact = None
        artifact_filename = None
        
        if sol.get('artifact'):
            artifact_filename = sol['artifact']
        elif sol['disproof']:
            artifact_filename = sol['disproof']
        elif sol['proof']:
            artifact_filename = sol['proof']
        elif sol['formalization']:
            artifact_filename = sol['formalization']
        
        if artifact_filename:
            # Construct path to the artifact file
            list_name = sol.get('list', 'unknown')
            problem_num = sol['number']
            file_path = f"problems/{list_name}/problem_{problem_num}/{artifact_filename}"
            # URL-encode the path for markdown links (handle spaces and special chars)
            from urllib.parse import quote
            encoded_path = quote(file_path, safe='/')
            # Create markdown link with code formatting
            artifact = f"[`{artifact_filename}`]({encoded_path})"
        else:
            artifact = "N/A"

        # Get status display
        status = get_status_display(sol)

        # Human review status
        if sol['review']:
            review = sol['review']
        else:
            review = "Pending"

        if show_list_column:
            list_name = sol.get('list', 'unknown')
            table += f"| {sol['number']} | {list_name} | {artifact} | {status} | {review} |\n"
        else:
            table += f"| {sol['number']} | {artifact} | {status} | {review} |\n"

    return table


def generate_readme(list_name: Optional[str] = None) -> str:
    """Generate complete README.md content.
    
    Args:
        list_name: Specific problem list to include, or None for all lists
    """
    from datetime import datetime, timezone
    
    # Read existing README sections (if any) - for now, start fresh
    readme = "# 🔮 BuddenBench: A Benchmark of Open Nontrivial Mathematics Research Problems\n\n"
    readme += "This benchmark, affectionately named [`budden-bench`]"
    readme += "(https://x.com/maxvonhippel/status/2014475901384241286?s=20), "
    readme += "measures the ability of models and agents to autonomously solve open and important problems "
    readme += "in mathematics research. In contrast to other problem sets such as the "
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
    solutions = scan_problem_solutions(list_name)
    if solutions:
        # Show list column if scanning all lists
        show_list_column = (list_name is None)
        readme += generate_solution_table(solutions, show_list_column)
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
    
    readme += "## Problem Sets\n\n"
    readme += "Problems are drawn from multiple sources:\n\n"
    readme += "- **[Kourovka Notebook](https://kourovka-notebook.org/)**: "
    readme += "A collection of unsolved problems in group theory\n"
    readme += "- **[Unsolved Problems in Intuitive Geometry](https://sites.math.washington.edu//~reu/papers/2010/mark/Unsolved_Problems_In_Intuitive_Geometry.pdf)** by Klee & Wagon: "
    readme += "Open problems in computational and combinatorial geometry\n"
    readme += "- **[100 Open Problems](https://arxiv.org/abs/2404.07513)** by Ben Green: "
    readme += "Research-level problems in additive combinatorics and number theory\n"
    readme += "- **Some open problems in analysis** by A.G. Ramm: "
    readme += "Open problems in Radon transforms, operator theory, and PDEs\n\n"
    
    # Add citation section
    readme += "## Citation\n\n"
    readme += "If you use this benchmark in your research, please cite:\n\n"
    readme += "```bibtex\n"
    readme += "@dataset{vonhippel2025budden,\n"
    readme += "  author={von Hippel, Max},\n"
    readme += "  title={{BuddenBench}: A Benchmark of Open Nontrivial Mathematics Research Problems},\n"
    readme += "  year={2025},\n"
    readme += "  publisher={GitHub},\n"
    readme += "  howpublished={\\url{https://github.com/maxvonhippel/budden-bench}},\n"
    readme += "  note={AI benchmark for automated mathematics research in group theory and geometry}\n"
    readme += "}\n"
    readme += "```\n\n"
    
    # Add last updated timestamp
    now = datetime.now(timezone.utc)
    timestamp = now.strftime("%Y-%m-%d %H:%M:%S UTC")
    readme += f"For citations to the source problem collections, see [references.bib](references.bib).\n\n"
    readme += f"*Last updated: {timestamp}*\n"
    
    return readme


def main() -> None:
    """Generate and write README.md."""
    import argparse
    parser = argparse.ArgumentParser(description="Generate README.md")
    parser.add_argument("--list", dest="list_name", default=None,
                       help="Problem list name (default: all lists)")
    args = parser.parse_args()
    
    readme_content = generate_readme(args.list_name)
    
    project_root = Path(__file__).parent.parent
    readme_path = project_root / "README.md"
    
    readme_path.write_text(readme_content)
    print(f"Generated {readme_path}")


if __name__ == '__main__':
    main()