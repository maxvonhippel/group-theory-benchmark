"""
Test the GAP query agent with diverse natural language queries.

Tests queries that haven't been explored before to validate the agent's ability
to generate correct GAP code from English.
"""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent.parent))

from src.tools.gap_query_agent import query_gap


def print_result(query: str, result):
    """Print formatted result."""
    print(f"\nQuery: {query}")
    print(f"Success: {result.success}")
    if result.success:
        print(f"Answer: {result.result_value}")
        print(f"GAP Code: {result.final_code}")
        print(f"Attempts: {result.attempts}")
    else:
        print(f"Error: {result.error}")
        print(f"Attempted code: {result.final_code}")
        print(f"Attempts: {result.attempts}")
    print("-" * 70)


def main():
    print("=" * 70)
    print("GAP Query Agent - Diverse Test Queries")
    print("=" * 70)

    # Test queries - all NEW, not explored before
    queries = [
        # Query 1: Order of center
        "What is the order of the center of the alternating group A_5?",

        # Query 2: Counting groups with SmallGroups
        "How many non-abelian groups of order 16 exist?",

        # Query 3: Property check with specific group
        "Is the quaternion group Q_8 nilpotent?",

        # Query 4: Derived subgroup
        "Find the order of the derived subgroup of the symmetric group S_5",

        # Query 5: Conjugacy classes
        "How many conjugacy classes does the alternating group A_6 have?",

        # Query 6: Prime order groups
        "Are all groups of order 17 cyclic?",

        # Query 7: Direct product
        "What is the order of the direct product of C_3 and C_4?",

        # Query 8: Checking isomorphism
        "Is the cyclic group C_6 isomorphic to the direct product C_2 times C_3?",
    ]

    for query in queries:
        result = query_gap(query, max_attempts=5)
        print_result(query, result)

    print("=" * 70)
    print("Test complete!")
    print("=" * 70)


if __name__ == "__main__":
    main()
