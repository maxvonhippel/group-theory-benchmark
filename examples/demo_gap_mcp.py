"""
Demo script showing how to use the GAP MCP server tools.

This demonstrates the high-level abstractions available for
group theory exploration without needing GAP syntax knowledge.
"""

import asyncio
import json
import sys
from pathlib import Path

# Add src to path
sys.path.insert(0, str(Path(__file__).parent.parent))

from src.tools.gap_mcp_server import call_tool


async def demo_check_properties():
    """Demonstrate checking group properties."""
    print("=" * 70)
    print("DEMO: Checking Group Properties")
    print("=" * 70)
    print()

    print("1. Is the symmetric group S_4 abelian?")
    result = await call_tool("check_group_property", {
        "group": "SymmetricGroup(4)",
        "property": "abelian"
    })
    data = json.loads(result[0].text)
    print(f"   Result: {data['data']['explanation']}")
    print()

    print("2. Is the cyclic group C_12 cyclic?")
    result = await call_tool("check_group_property", {
        "group": "CyclicGroup(12)",
        "property": "cyclic"
    })
    data = json.loads(result[0].text)
    print(f"   Result: {data['data']['explanation']}")
    print()

    print("3. Is the alternating group A_5 simple?")
    result = await call_tool("check_group_property", {
        "group": "AlternatingGroup(5)",
        "property": "simple"
    })
    data = json.loads(result[0].text)
    print(f"   Result: {data['data']['explanation']}")
    print()


async def demo_find_counterexamples():
    """Demonstrate finding counterexamples."""
    print("=" * 70)
    print("DEMO: Finding Counterexamples")
    print("=" * 70)
    print()

    print("1. Find a non-abelian group")
    result = await call_tool("find_counterexample", {
        "property": "abelian",
        "max_order": 20
    })
    data = json.loads(result[0].text)
    if data["data"]["counterexamples"]:
        examples = data["data"]["counterexamples"][:3]
        print(f"   Found {len(examples)} examples:")
        for ex in examples:
            print(f"   - {ex['group']} (order {ex['order']})")
    print()

    print("2. Find a solvable but not nilpotent group")
    result = await call_tool("find_counterexample", {
        "property": "nilpotent",
        "additional_condition": "solvable",
        "max_order": 30
    })
    data = json.loads(result[0].text)
    if data["data"]["counterexamples"]:
        examples = data["data"]["counterexamples"][:2]
        print(f"   Found {len(examples)} examples:")
        for ex in examples:
            print(f"   - {ex['group']} (order {ex['order']})")
    print()


async def demo_compute_invariants():
    """Demonstrate computing group invariants."""
    print("=" * 70)
    print("DEMO: Computing Group Invariants")
    print("=" * 70)
    print()

    groups = ["SymmetricGroup(4)", "AlternatingGroup(4)", "CyclicGroup(12)"]

    for group in groups:
        print(f"Invariants of {group}:")
        result = await call_tool("compute_group_invariants", {"group": group})
        data = json.loads(result[0].text)
        inv = data["data"]["invariants"]

        print(f"  Order: {inv.get('order', 'N/A')}")
        print(f"  Center order: {inv.get('center_order', 'N/A')}")
        print(f"  Derived subgroup order: {inv.get('derived_subgroup_order', 'N/A')}")
        print(f"  Conjugacy classes: {inv.get('num_conjugacy_classes', 'N/A')}")
        print("  Properties:")
        for prop, value in inv.get("properties", {}).items():
            print(f"    {prop}: {value}")
        print()


async def demo_search_small_groups():
    """Demonstrate searching the SmallGroups library."""
    print("=" * 70)
    print("DEMO: Searching Small Groups Library")
    print("=" * 70)
    print()

    print("1. All groups of order 8")
    result = await call_tool("search_small_groups", {"order": 8})
    data = json.loads(result[0].text)
    if data.get('success'):
        print(f"   Total groups of order 8: {data['data']['total_groups']}")
        print(f"   Groups listed: {len(data['data']['groups'])}")
    else:
        print(f"   Error: {data.get('error', 'Unknown error')}")
    print()

    print("2. Abelian groups of order 12")
    result = await call_tool("search_small_groups", {
        "order": 12,
        "property": "abelian"
    })
    data = json.loads(result[0].text)
    if data.get('success'):
        print(f"   Total groups of order 12: {data['data']['total_groups']}")
        print(f"   Abelian groups of order 12: {len(data['data']['groups'])}")
        for g in data["data"]["groups"]:
            print(f"   - {g['group']}")
    else:
        print(f"   Error: {data.get('error', 'Unknown error')}")
    print()


async def demo_compare_groups():
    """Demonstrate comparing groups."""
    print("=" * 70)
    print("DEMO: Comparing Groups")
    print("=" * 70)
    print()

    comparisons = [
        ("CyclicGroup(4)", "SmallGroup(4, 1)", "C_4 and first group of order 4"),
        ("SymmetricGroup(3)", "SmallGroup(6, 2)", "S_3 and second group of order 6"),
        ("CyclicGroup(6)", "SmallGroup(6, 1)", "C_6 and first group of order 6"),
    ]

    for g1, g2, description in comparisons:
        print(f"Comparing {description}:")
        result = await call_tool("compare_groups", {
            "group1": g1,
            "group2": g2
        })
        data = json.loads(result[0].text)
        comp = data["data"]

        print(f"  Isomorphic: {comp['are_isomorphic']}")
        print("  Properties:")
        for prop, values in comp.get("properties", {}).items():
            match = "✓" if values["same"] else "✗"
            print(f"    {prop}: {values['group1']} vs {values['group2']} {match}")
        print()


async def demo_test_conjecture():
    """Demonstrate testing conjectures on small groups."""
    print("=" * 70)
    print("DEMO: Testing Conjectures")
    print("=" * 70)
    print()

    properties = ["abelian", "cyclic", "simple"]

    for prop in properties:
        print(f"Testing: What percentage of small groups are {prop}?")
        result = await call_tool("test_conjecture_on_small_groups", {
            "property": prop,
            "max_order": 30
        })
        data = json.loads(result[0].text)
        stats = data["data"]["statistics"]

        print(f"  Tested: {stats['total_tested']} groups")
        print(f"  {prop.capitalize()}: {stats['satisfies_property']} ({data['data']['percentage_satisfying']}%)")
        print(f"  Not {prop}: {stats['fails_property']}")
        print()


async def demo_raw_gap():
    """Demonstrate raw GAP evaluation for advanced users."""
    print("=" * 70)
    print("DEMO: Raw GAP Evaluation (Advanced)")
    print("=" * 70)
    print()

    commands = [
        ("2^10", "Basic arithmetic"),
        ("Size(Centre(SymmetricGroup(4)))", "Center size of S_4"),
        ("Factorial(20)", "Large factorial"),
        ("IsPrime(97)", "Primality test"),
    ]

    for code, description in commands:
        print(f"{description}: {code}")
        result = await call_tool("evaluate_gap", {"code": code})
        data = json.loads(result[0].text)
        print(f"  Result: {data['data']['result']}")
    print()


async def main():
    """Run all demos."""
    print()
    print("=" * 70)
    print("GAP MCP Server - Interactive Demo")
    print("=" * 70)
    print()
    print("This demo shows high-level abstractions for computational group theory")
    print("No GAP syntax knowledge required!")
    print()

    try:
        await demo_check_properties()
        await demo_find_counterexamples()
        await demo_compute_invariants()
        await demo_search_small_groups()
        await demo_compare_groups()
        await demo_test_conjecture()
        await demo_raw_gap()

        print("=" * 70)
        print("Demo completed successfully!")
        print("=" * 70)

    except Exception as e:
        print(f"\nDemo failed: {e}")
        import traceback
        traceback.print_exc()


if __name__ == "__main__":
    asyncio.run(main())
