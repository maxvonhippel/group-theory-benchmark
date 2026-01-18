"""
Generate a tree structure of the project with comments from Python files.

This script creates a visual tree representation of the directory structure,
including docstrings from Python files as inline comments.
"""

import os
from pathlib import Path


def get_first_line(filepath: Path) -> str:
    """Extract the first line of a docstring from a Python file."""
    try:
        with open(filepath, 'r', encoding='utf-8') as f:
            content = f.read()
            # Find module docstring
            if content.startswith('"""') or content.startswith("'''"):
                quote = '"""' if content.startswith('"""') else "'''"
                try:
                    end_idx = content.index(quote, 3)
                    docstring = content[3:end_idx].strip()
                    # Get first meaningful line
                    for line in docstring.split('\n'):
                        line = line.strip()
                        if line and not line.startswith('#'):
                            return line
                except ValueError:
                    pass
    except Exception:
        pass
    return ""


def should_skip(path: Path, name: str) -> bool:
    """Check if a path should be skipped in the tree."""
    skip_dirs = {
        '__pycache__', '.git', '.venv', 'node_modules', 
        '.pytest_cache', '.mypy_cache', '.ruff_cache',
        'baml_client',  # Generated code
        'problems',  # Generated problem folders (2000+)
        '_build', 'build', 'dist', '*.egg-info'
    }
    skip_files = {
        '.DS_Store', '*.pyc', '*.pyo', '*.pyd', '.gitignore',
        'uv.lock', '.python-version'
    }
    
    if name in skip_dirs:
        return True
    if name in skip_files:
        return True
    if name.startswith('.') and name not in {'.cursorrules'}:
        return True
    
    # Skip gap submodule internals
    if 'gap/' in str(path) and name not in {'gap',  'doc', 'lib'}:
        return True
    
    return False


def print_tree(directory: Path, prefix: str = "", max_depth: int = 3, current_depth: int = 0):
    """Print directory tree with docstring comments."""
    if current_depth >= max_depth:
        return
    
    try:
        entries = sorted(directory.iterdir(), key=lambda x: (not x.is_dir(), x.name))
    except PermissionError:
        return
    
    entries = [e for e in entries if not should_skip(e, e.name)]
    
    for i, entry in enumerate(entries):
        is_last = i == len(entries) - 1
        current_prefix = "└── " if is_last else "├── "
        next_prefix = "    " if is_last else "│   "
        
        comment = ""
        if entry.is_file() and entry.suffix == '.py':
            first_line = get_first_line(entry)
            if first_line:
                comment = f"  # {first_line}"
        
        print(f"{prefix}{current_prefix}{entry.name}{comment}")
        
        if entry.is_dir():
            print_tree(entry, prefix + next_prefix, max_depth, current_depth + 1)


if __name__ == "__main__":
    project_root = Path(__file__).parent.parent
    print(f"{project_root.name}/")
    print_tree(project_root, "", max_depth=4)