"""Migrate legacy formalization_attempt_summary.txt files to cannot_formalize.txt format."""

from pathlib import Path
import re


def extract_reason_from_summary(summary_path: Path) -> str:
    """Extract concise reason from verbose formalization_attempt_summary.txt."""
    content = summary_path.read_text()
    
    # Look for section headers that indicate why formalization failed
    section_patterns = [
        r"WHY FORMALIZATION IS INFEASIBLE:.*?\n-+\n(.+?)(?=\n\n[A-Z]|\Z)",
        r"REASON FOR INABILITY TO FORMALIZE:.*?\n-+\n(.+?)(?=\n\n[A-Z]|\Z)",
        r"STATUS:.*?COULD NOT BE FORMALIZED.*?\n-+\n(.+?)(?=\n\n[A-Z]|\Z)",
        r"This problem cannot currently be formalized in Lean because:\s*\n(.+?)(?=\n\n[A-Z]|\Z)",
    ]
    
    for pattern in section_patterns:
        match = re.search(pattern, content, re.IGNORECASE | re.DOTALL)
        if match:
            reason = match.group(1).strip()
            # Take first paragraph/sentence of the reason
            lines = reason.split('\n')
            # Get first few non-empty lines
            substantial_lines = []
            for line in lines:
                line = line.strip()
                if line and not line.startswith('---') and not line.startswith('==='):
                    # Skip numbered lists headers, get the content
                    if re.match(r'^\d+\.', line):
                        substantial_lines.append(line)
                    elif substantial_lines:  # Continue building reason
                        substantial_lines.append(line)
                    else:
                        substantial_lines.append(line)
                    
                    # Stop after getting enough content
                    if len(' '.join(substantial_lines)) > 200:
                        break
            
            reason = ' '.join(substantial_lines)
            # Clean up
            reason = re.sub(r'\s+', ' ', reason)
            if len(reason) > 400:
                reason = reason[:397] + "..."
            return reason
    
    # Last resort: look for the problem statement itself which explains the issue
    statement_match = re.search(r"PROBLEM STATEMENT:.*?\n(.+?)(?=\n\n[A-Z]|\Z)", content, re.DOTALL)
    if statement_match:
        return f"This problem could not be formalized. Problem asks: {statement_match.group(1).strip()[:200]}..."
    
    return "This problem could not be formalized. See formalization_attempt_summary.txt for details."


def main():
    problems_dir = Path("problems")
    
    # Find all legacy files
    legacy_files = list(problems_dir.glob("*/formalization_attempt_summary.txt"))
    
    print(f"Found {len(legacy_files)} legacy formalization_attempt_summary.txt files:")
    for f in legacy_files:
        print(f"  {f.parent.name}")
    
    print("\nMigrating to cannot_formalize.txt format...")
    
    migrated = 0
    for summary_path in legacy_files:
        problem_dir = summary_path.parent
        cannot_formalize_path = problem_dir / "cannot_formalize.txt"
        
        if cannot_formalize_path.exists():
            print(f"  {problem_dir.name}: cannot_formalize.txt already exists, skipping")
            continue
        
        # Extract concise reason
        reason = extract_reason_from_summary(summary_path)
        
        # Write new format file
        cannot_formalize_path.write_text(reason)
        
        # Keep the old file for reference (can be deleted later if needed)
        # summary_path.unlink()
        
        print(f"  {problem_dir.name}: Migrated")
        print(f"    Reason: {reason[:100]}...")
        migrated += 1
    
    print(f"\nMigrated {migrated} files to new format")
    print("Legacy formalization_attempt_summary.txt files preserved for reference")
    
    return 0


if __name__ == "__main__":
    exit(main())