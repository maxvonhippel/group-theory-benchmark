#!/usr/bin/env python3
"""PDF problem extractor that writes clean JSON to a file."""
import sys
import json
import asyncio
import os
from pathlib import Path
import pymupdf

# Disable BAML logging
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
    if len(sys.argv) < 3:
        print("Usage: uv run src/extract_clean.py <pdf_path> <output_json> [start_page] [end_page]", file=sys.stderr)
        sys.exit(1)
    
    pdf_path = sys.argv[1]
    output_path = sys.argv[2]
    
    # Open PDF to get page count
    doc = pymupdf.open(pdf_path)
    total_pages = len(doc)
    doc.close()
    
    # Parse start and end pages (0-indexed internally, 1-indexed for user)
    start_page = int(sys.argv[3]) - 1 if len(sys.argv) > 3 else 0
    end_page = int(sys.argv[4]) - 1 if len(sys.argv) > 4 else total_pages - 1
    
    print(f"Extracting problems from pages {start_page + 1} to {end_page + 1} of {total_pages}", file=sys.stderr)
    
    # Process pages in parallel batches to avoid overwhelming the API
    batch_size = 20  # Process 20 pages at a time
    all_problems = []
    
    for batch_start in range(start_page, end_page + 1, batch_size):
        batch_end = min(batch_start + batch_size, end_page + 1)
        print(f"Processing pages {batch_start + 1}-{batch_end}...", file=sys.stderr)
        
        # Process this batch in parallel
        tasks = [extract_problems_from_page(pdf_path, page_num) 
                 for page_num in range(batch_start, batch_end)]
        batch_results = await asyncio.gather(*tasks)
        
        # Flatten and add to all_problems
        for problems in batch_results:
            all_problems.extend(problems)
        
        print(f"  Completed batch. Total problems so far: {len(all_problems)}", file=sys.stderr)
    
    # Write JSON directly to file
    with open(output_path, 'w') as f:
        json.dump(all_problems, f, indent=2, ensure_ascii=False)
    
    print(f"\nExtraction complete: {len(all_problems)} problems written to {output_path}", file=sys.stderr)


if __name__ == "__main__":
    asyncio.run(main())