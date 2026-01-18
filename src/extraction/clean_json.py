#!/usr/bin/env python3
"""Helper script to extract clean JSON from BAML-polluted output."""
import sys
import re

def extract_json(input_file, output_file):
    """Extract JSON array from file containing BAML logs."""
    with open(input_file, 'r') as f:
        content = f.read()
    
    # Find the start of the JSON array
    match = re.search(r'^\[', content, re.MULTILINE)
    if match:
        json_content = content[match.start():]
        with open(output_file, 'w') as f:
            f.write(json_content)
        return True
    return False

if __name__ == "__main__":
    if len(sys.argv) != 3:
        print("Usage: python clean_json.py <input_file> <output_file>")
        sys.exit(1)
    
    if extract_json(sys.argv[1], sys.argv[2]):
        print(f"Cleaned JSON written to {sys.argv[2]}")
    else:
        print("Error: Could not find JSON array in input")
        sys.exit(1)