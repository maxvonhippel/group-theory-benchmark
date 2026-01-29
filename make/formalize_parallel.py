"""Parallel batch formalization of problems using Claude."""

import json
import sys
import multiprocessing
from pathlib import Path
from typing import List, Dict, Any
import subprocess

def formalize_single_problem(args):
    """Run formalize_problem.py on a single problem.
    
    Args:
        args: Tuple of (problem_num, list_name, project_root)
    
    Returns:
        Dict with problem_num, success status, and error message if any
    """
    problem_num, list_name, project_root = args
    
    try:
        result = subprocess.run(
            ['uv', 'run', 'python', 'make/formalize_problem.py', str(problem_num), '--list', list_name],
            cwd=project_root,
            capture_output=True,
            text=True,
            timeout=360  # 6 minutes max (5 min Claude + 1 min overhead)
        )
        
        success = result.returncode == 0
        return {
            'problem_num': problem_num,
            'success': success,
            'stdout': result.stdout,
            'stderr': result.stderr
        }
    except subprocess.TimeoutExpired:
        return {
            'problem_num': problem_num,
            'success': False,
            'error': 'Process timeout (6 minutes)'
        }
    except Exception as e:
        return {
            'problem_num': problem_num,
            'success': False,
            'error': str(e)
        }

def load_problems(list_name: str) -> List[Dict[str, Any]]:
    """Load all problems from JSON for a specific problem list."""
    problems_file = Path(f"problems/{list_name}/all_problems.json")
    if not problems_file.exists():
        print(f"Error: problems/{list_name}/all_problems.json not found")
        sys.exit(1)
    
    with open(problems_file) as f:
        return json.load(f)

def get_unformalized_problems(list_name: str, n: int) -> List[str]:
    """Get first N unformalized problem numbers.
    
    Args:
        list_name: Name of the problem list
        n: Number of problems to get
    
    Returns:
        List of problem numbers as strings
    """
    problems = load_problems(list_name)
    unformalized = []
    
    for problem in problems:
        problem_num = problem.get('problem_number')
        if not problem_num:
            continue
        
        # Check if already formalized
        problem_dir = Path(f"problems/{list_name}/problem_{problem_num}")
        formalization_file = problem_dir / "formalization.lean"
        cannot_file = problem_dir / "cannot_formalize.txt"
        
        if not formalization_file.exists() and not cannot_file.exists():
            unformalized.append(str(problem_num))
            
            if len(unformalized) >= n:
                break
    
    return unformalized

def main():
    import argparse
    parser = argparse.ArgumentParser(description="Parallel batch formalization of problems")
    parser.add_argument("--n", type=int, required=True, help="Number of problems to formalize")
    parser.add_argument("--batch", type=int, default=10, help="Batch size (number of parallel instances)")
    parser.add_argument("--list", dest="list_name", default="kourovka", help="Problem list name")
    args = parser.parse_args()
    
    list_name = args.list_name
    n = args.n
    batch_size = args.batch
    
    # Get project root
    project_root = Path.cwd()
    
    # Get unformalized problems
    print(f"Finding first {n} unformalized problems from {list_name}...")
    problem_nums = get_unformalized_problems(list_name, n)
    
    if not problem_nums:
        print(f"No unformalized problems found in {list_name}")
        sys.exit(0)
    
    total_problems = len(problem_nums)
    print(f"Found {total_problems} unformalized problems")
    print(f"Running in batches of {batch_size}")
    print("=" * 60)
    
    # Process in batches
    all_results = []
    for i in range(0, total_problems, batch_size):
        batch = problem_nums[i:i+batch_size]
        batch_num = i // batch_size + 1
        total_batches = (total_problems + batch_size - 1) // batch_size
        
        print(f"\nBatch {batch_num}/{total_batches}: Processing {len(batch)} problems")
        print(f"Problems: {', '.join(batch)}")
        print("-" * 60)
        
        # Prepare args for multiprocessing
        batch_args = [(prob_num, list_name, str(project_root)) for prob_num in batch]
        
        # Run batch in parallel
        with multiprocessing.Pool(processes=len(batch)) as pool:
            batch_results = pool.map(formalize_single_problem, batch_args)
        
        all_results.extend(batch_results)
        
        # Print batch summary
        successes = sum(1 for r in batch_results if r['success'])
        print(f"\nBatch {batch_num} complete: {successes}/{len(batch)} succeeded")
    
    # Final summary
    print("\n" + "=" * 60)
    print("FINAL SUMMARY")
    print("=" * 60)
    
    successes = sum(1 for r in all_results if r['success'])
    failures = total_problems - successes
    
    print(f"Total problems: {total_problems}")
    print(f"Succeeded: {successes}")
    print(f"Failed: {failures}")
    
    if failures > 0:
        print("\nFailed problems:")
        for r in all_results:
            if not r['success']:
                error_msg = r.get('error', 'Unknown error')
                print(f"  - {r['problem_num']}: {error_msg}")
    
    print("=" * 60)

if __name__ == "__main__":
    main()