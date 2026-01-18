"""
Test the GAP MCP on real Kourovka Notebook problems.

This tests if our MCP tools are useful for exploring open research problems.
"""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent.parent))

from src.tools.gap_query_agent import query_gap


def test_problem_1_40():
    """
    Problem 1.40: Is a group a nilgroup if it is the product of two normal nilsubgroups?

    A nilgroup consists of nilelements (Engel elements).

    Let's use GAP to:
    1. Check if small groups that are products of normal nilpotent subgroups are nilpotent
    2. Look for counterexamples
    """
    print("=" * 80)
    print("Problem 1.40: Product of two normal nilsubgroups")
    print("=" * 80)

    # First, let's understand the property better with small examples
    queries = [
        "Is the direct product of two nilpotent groups always nilpotent?",
        "Give an example of a non-nilpotent group of order 24",
        "How many nilpotent groups of order 24 exist?",
        "What is an example of a solvable but not nilpotent group?",
    ]

    for query in queries:
        print(f"\nQuery: {query}")
        result = query_gap(query)
        if result.success:
            print(f"Answer: {result.result_value}")
            print(f"GAP Code: {result.final_code}")
        else:
            print(f"Failed: {result.error}")
        print("-" * 80)


def test_problem_1_31():
    """
    Problem 1.31: Is a residually finite group with the maximum condition
    for subgroups almost polycyclic?

    Let's explore properties of small groups.
    """
    print("\n" + "=" * 80)
    print("Problem 1.31: Residually finite groups")
    print("=" * 80)

    queries = [
        "Is the symmetric group S_5 residually finite?",
        "Is the alternating group A_5 polycyclic?",
        "Give an example of a polycyclic group",
        "Is every finite group residually finite?",
    ]

    for query in queries:
        print(f"\nQuery: {query}")
        result = query_gap(query)
        if result.success:
            print(f"Answer: {result.result_value}")
            print(f"GAP Code: {result.final_code}")
        else:
            print(f"Failed: {result.error}")
        print("-" * 80)


def test_engel_groups():
    """
    Problem 2.25 relates to Engel groups being orderable.
    Let's explore Engel conditions computationally.
    """
    print("\n" + "=" * 80)
    print("Exploring Engel Groups")
    print("=" * 80)

    queries = [
        "Is the quaternion group Q_8 an Engel group?",
        "Check if all abelian groups are 1-Engel groups",
        "What is the nilpotency class of the dihedral group D_8?",
    ]

    for query in queries:
        print(f"\nQuery: {query}")
        result = query_gap(query)
        if result.success:
            print(f"Answer: {result.result_value}")
            print(f"GAP Code: {result.final_code}")
        else:
            print(f"Failed: {result.error}")
        print("-" * 80)


def test_group_property_exploration():
    """
    Test the MCP's ability to help explore group properties systematically.
    """
    print("\n" + "=" * 80)
    print("Systematic Property Exploration")
    print("=" * 80)

    queries = [
        "List all non-abelian simple groups of order less than 100",
        "How many solvable groups of order 16 are there?",
        "Find the smallest non-abelian group that is not solvable",
        "What is the derived length of the symmetric group S_4?",
        "Are there any perfect groups of order 12?",
    ]

    for query in queries:
        print(f"\nQuery: {query}")
        result = query_gap(query)
        if result.success:
            print(f"Answer: {result.result_value}")
            print(f"GAP Code: {result.final_code}")
            print(f"Explanation: {result.explanation}")
        else:
            print(f"Failed: {result.error}")
        print("-" * 80)


def main():
    print("Testing GAP MCP on Real Kourovka Notebook Problems")
    print("=" * 80)

    # Test different problem areas
    test_problem_1_40()
    test_problem_1_31()
    test_engel_groups()
    test_group_property_exploration()

    print("\n" + "=" * 80)
    print("MCP Testing Complete")
    print("=" * 80)


if __name__ == "__main__":
    main()
