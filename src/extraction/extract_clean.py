"""PDF problem extractor that writes clean JSON to a file.
Supports multiple problem list formats (Kourovka, Klee geometry, etc.)
"""
import sys
import json
import asyncio
import os
import argparse
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


async def extract_problems_from_page(pdf_path: str, page_num: int, list_format: str = "kourovka") -> list[dict]:
    """Extract all math problems from a specific page using the appropriate format."""
    page_text = extract_page_text(pdf_path, page_num)
    
    # Use BAML to extract problems based on format
    if list_format == "klee":
        result = await b.ExtractKleeProblems(page_text=page_text, page_number=page_num + 1)
    else:  # default to kourovka
        result = await b.ExtractKourovkaProblems(page_text=page_text, page_number=page_num + 1)
    
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
    parser = argparse.ArgumentParser(description="Extract problems from PDF")
    parser.add_argument("pdf_path", help="Path to PDF file")
    parser.add_argument("output_json", help="Path to output JSON file")
    parser.add_argument("start_page", type=int, nargs="?", default=1, help="Start page (1-indexed, default: 1)")
    parser.add_argument("end_page", type=int, nargs="?", help="End page (1-indexed, default: last page)")
    parser.add_argument("--list", dest="list_format", default="kourovka", 
                       choices=["kourovka", "klee"],
                       help="Problem list format (default: kourovka)")
    args = parser.parse_args()
    
    pdf_path = args.pdf_path
    output_path = args.output_json
    list_format = args.list_format
    
    # Open PDF to get page count
    doc = pymupdf.open(pdf_path)
    total_pages = len(doc)
    doc.close()
    
    # Parse start and end pages (0-indexed internally, 1-indexed for user)
    start_page = args.start_page - 1
    end_page = (args.end_page - 1) if args.end_page else (total_pages - 1)
    
    print(f"Extracting {list_format} problems from pages {start_page + 1} to {end_page + 1} of {total_pages}", file=sys.stderr)
    
    # Process pages in parallel batches to avoid overwhelming the API
    batch_size = 20  # Process 20 pages at a time
    all_problems = []
    
    for batch_start in range(start_page, end_page + 1, batch_size):
        batch_end = min(batch_start + batch_size, end_page + 1)
        print(f"Processing pages {batch_start + 1}-{batch_end}...", file=sys.stderr)
        
        # Process this batch in parallel
        tasks = [extract_problems_from_page(pdf_path, page_num, list_format) 
                 for page_num in range(batch_start, batch_end)]
        batch_results = await asyncio.gather(*tasks)
        
        # Flatten and add to all_problems
        for problems in batch_results:
            all_problems.extend(problems)
        
        print(f"  Completed batch. Total problems so far: {len(all_problems)}", file=sys.stderr)
    
    # Write JSON directly to file (ensure parent directory exists)
    output_file = Path(output_path)
    output_file.parent.mkdir(parents=True, exist_ok=True)
    with open(output_file, 'w') as f:
        json.dump(all_problems, f, indent=2, ensure_ascii=False)
    
    print(f"\nExtraction complete: {len(all_problems)} problems written to {output_path}", file=sys.stderr)


if __name__ == "__main__":
    asyncio.run(main())