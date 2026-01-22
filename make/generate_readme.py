#!/usr/bin/env python3
"""
Generate README.md with automated solution tracking table.
"""
from pathlib import Path


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
            'review': None
        }

        # Check for solution artifacts
        disproof_file = problem_dir / "disproof.py"
        proof_file = problem_dir / "proof.lean"
        formalization_file = problem_dir / "problem.lean"
        attempt_summary_file = problem_dir / "formalization_attempt_summary.txt"
        review_file = problem_dir / "review.txt"

        if disproof_file.exists():
            solution_info['disproof'] = 'disproof.py'
        if proof_file.exists():
            solution_info['proof'] = 'proof.lean'
        if formalization_file.exists():
            solution_info['formalization'] = 'problem.lean'
        if attempt_summary_file.exists():
            solution_info['attempt_summary'] = 'formalization_attempt_summary.txt'
        
        # Check for human review
        if review_file.exists():
            review_text = review_file.read_text().strip()
            if len(review_text) > 10:
                solution_info['review'] = review_text[:10].strip() + "..."
            else:
                solution_info['review'] = review_text
        
        # Only include if there's at least one artifact
        if any([solution_info['disproof'], solution_info['proof'], solution_info['formalization'], solution_info['attempt_summary']]):
            solutions.append(solution_info)
    
    return solutions


def generate_solution_table(solutions):
    """Generate markdown table for solutions."""
    if not solutions:
        return ""
    
    table = "\n## AI-Generated Solutions\n\n"
    table += "**⚠️ WARNING**: [No AI-generated proof should be trusted without human review, no matter how formal.] "
    table += "(https://www.lesswrong.com/posts/rhAPh3YzhPoBNpgHg/lies-damned-lies-and-proofs-formal-methods-are-not-slopless)\n\n"
    
    table += "| Problem | Artifact | Human Review |\n"
    table += "|---------|----------|-------------|\n"
    
    for sol in solutions:
        # Determine solution type
        if sol['disproof']:
            solution = f"`{sol['disproof']}` (GAP counterexample)"
        elif sol['proof']:
            solution = f"`{sol['proof']}` (Lean proof)"
        elif sol['formalization']:
            solution = f"`{sol['formalization']}` (formalization only)"
        elif sol['attempt_summary']:
            solution = f"`{sol['attempt_summary']}` (could not formalize)"
        else:
            solution = "N/A"
        
        # Human review status
        if sol['review']:
            review = sol['review']
        else:
            review = "❌"
        
        table += f"| {sol['number']} | {solution} | {review} |\n"
    
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