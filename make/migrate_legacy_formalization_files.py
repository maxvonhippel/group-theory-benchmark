"""Migrate legacy formalization_attempt_summary.txt files to cannot_formalize.txt format."""

from pathlib import Path
import re


def extract_reason_from_summary(summary_path: Path) -> str:
    """Extract concise reason from verbose formalization_attempt_summary.txt."""
    content = summary_path.read_text()
    
    # Look for common patterns indicating why formalization failed
    patterns = [
        r"CONCLUSION[:\s]+(.+?)(?=\n\n|\Z)",
        r"Why this problem cannot be formalized[:\s]+(.+?)(?=\n\n|\Z)",
        r"cannot be formalized because[:\s]+(.+?)(?=\n\n|\Z)",
        r"CANNOT BE FORMALIZED[:\s]+(.+?)(?=\n\n|\Z)",
    ]
    
    for pattern in patterns:
        match = re.search(pattern, content, re.IGNORECASE | re.DOTALL)
        if match:
            reason = match.group(1).strip()
            # Clean up excessive whitespace
            reason = re.sub(r'\s+', ' ', reason)
            # Limit to reasonable length
            if len(reason) > 500:
                reason = reason[:497] + "..."
            return reason
    
    # Fallback: use first paragraph after header
    lines = content.split('\n')
    non_empty_lines = [line.strip() for line in lines if line.strip() and not line.startswith('=')]
    if len(non_empty_lines) > 1:
        # Skip header, take next substantial content
        for line in non_empty_lines[1:]:
            if len(line) > 50:  # Substantial content
                if len(line) > 500:
                    return line[:497] + "..."
                return line
    
    # Last resort
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