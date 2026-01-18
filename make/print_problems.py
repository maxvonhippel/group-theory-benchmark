"""Print open or closed problems from the extraction."""
import json
import sys
import random
from pathlib import Path


def pretty_print_problem(problem: dict, index: int):
    """Pretty print a single problem."""
    print(f"\n{'='*80}")
    print(f"Problem #{index}: {problem['problem_number']} (Page {problem['page_number']})")
    print(f"{'='*80}")
    print(f"\n{problem['problem_text']}")
    
    if problem.get('answer'):
        print(f"\nAnswer: {problem['answer']}")


def main():
    if len(sys.argv) < 2:
        print("Usage: uv run make/print_problems.py <open|closed> [num=N] [random=true]", file=sys.stderr)
        sys.exit(1)
    
    problem_type = sys.argv[1]
    if problem_type not in ['open', 'closed']:
        print(f"Error: Problem type must be 'open' or 'closed', got '{problem_type}'", file=sys.stderr)
        sys.exit(1)
    
    # Parse optional arguments
    num = None
    use_random = False
    
    for arg in sys.argv[2:]:
        if arg.startswith('num='):
            num = int(arg.split('=')[1])
        elif arg.startswith('random='):
            use_random = arg.split('=')[1].lower() in ['true', '1', 'yes']
    
    # Load problems
    problems_file = Path('problems/all_problems.json')
    if not problems_file.exists():
        print("Error: problems/all_problems.json not found. Run 'make extract' first.", file=sys.stderr)
        sys.exit(1)
    
    with open(problems_file) as f:
        all_problems = json.load(f)
    
    # Filter by open/closed
    if problem_type == 'open':
        filtered = [p for p in all_problems if not p.get('answer')]
    else:
        filtered = [p for p in all_problems if p.get('answer')]
    
    total_count = len(filtered)
    
    # Validate arguments
    if use_random and num is None:
        print("Error: --random requires --num to be specified", file=sys.stderr)
        sys.exit(1)
    
    if num is not None and num > total_count:
        print(f"Error: num={num} is greater than total {problem_type} problems ({total_count})", file=sys.stderr)
        sys.exit(1)
    
    # Select problems to display
    if num is None:
        selected = filtered
    elif use_random:
        selected = random.sample(filtered, num)
    else:
        selected = filtered[:num]
    
    # Print problems
    print(f"\n{problem_type.upper()} PROBLEMS")
    print(f"{'='*80}")
    
    for i, problem in enumerate(selected, 1):
        pretty_print_problem(problem, i)
    
    # Print summary
    print(f"\n{'='*80}")
    if num is not None:
        print(f"Showing {len(selected)} of {total_count} {problem_type} problems")
    else:
        print(f"Total {problem_type} problems: {total_count}")
    print(f"{'='*80}\n")


if __name__ == "__main__":
    main()