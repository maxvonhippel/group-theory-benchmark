import sys
import json
import asyncio
import os
from pathlib import Path
import pymupdf

# Disable BAML logging before importing
os.environ['BAML_LOG'] = 'false'

from baml_client.baml_client import b


def extract_page_text(pdf_path: str, page_num: int) -> str:
    """Extract text from a specific page of a PDF."""
    doc = pymupdf.open(pdf_path)
    page = doc[page_num]
    text = page.get_text()
    doc.close()
    return text


async def extract_problems_from_page(pdf_path: str, page_num: int) -> list[dict]:
    """Extract all math problems from a specific page."""
    page_text = extract_page_text(pdf_path, page_num)
    
    # Use BAML to extract problems
    result = await b.ExtractProblems(page_text=page_text, page_number=page_num + 1)
    
    # Convert to list of dicts with page number added
    problems = []
    for problem in result.problems:
        problem_data = {
            "page_number": page_num + 1,
            "problem_number": problem.problem_number,
            "problem_text": problem.problem_text,
        }
        if problem.answer is not None:
            problem_data["answer"] = problem.answer
        problems.append(problem_data)
    
    return problems


async def main():
    if len(sys.argv) < 2:
        print("Usage: uv run src/extract.py <pdf_path> [start_page] [end_page]")
        sys.exit(1)
    
    pdf_path = sys.argv[1]
    
    # Open PDF to get page count
    doc = pymupdf.open(pdf_path)
    total_pages = len(doc)
    doc.close()
    
    # Parse start and end pages (0-indexed internally, 1-indexed for user)
    start_page = int(sys.argv[2]) - 1 if len(sys.argv) > 2 else 0
    end_page = int(sys.argv[3]) - 1 if len(sys.argv) > 3 else total_pages - 1
    
    print(f"Extracting problems from pages {start_page + 1} to {end_page + 1} of {total_pages}")
    
    all_problems = []
    for page_num in range(start_page, end_page + 1):
        print(f"Processing page {page_num + 1}...", file=sys.stderr)
        problems = await extract_problems_from_page(pdf_path, page_num)
        all_problems.extend(problems)
        print(f"  Found {len(problems)} problem(s)", file=sys.stderr)
    
    # Output all problems as JSON array
    print(json.dumps(all_problems, indent=2))


if __name__ == "__main__":
    asyncio.run(main())