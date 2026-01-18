"""
GAP MCP Server - Model Context Protocol server for GAP (Groups, Algorithms, Programming).

This MCP server provides high-level tools for computational group theory
without requiring knowledge of GAP syntax. It's designed for AI agents to
explore group theory, find counterexamples, and test conjectures.
"""

import asyncio
import json
from typing import Any, Optional
from mcp.server import Server
from mcp.server.stdio import stdio_server
from mcp.types import Tool, TextContent

from src.tools.gap import Gap, GapError
from src.tools.gap_query_agent import GAPQueryAgent


# Initialize GAP instance
gap = Gap()
# Initialize query agent
query_agent = GAPQueryAgent(max_attempts=5)

# Load SmallGrp package on startup
_smallgrp_loaded = False

def ensure_smallgrp():
    """Ensure SmallGrp package is loaded."""
    global _smallgrp_loaded
    if not _smallgrp_loaded:
        result = gap.eval('LoadPackage("SmallGrp")')
        _smallgrp_loaded = result.success and result.value
    return _smallgrp_loaded

# Initialize MCP server
app = Server("gap-server")


@app.list_tools()
async def list_tools() -> list[Tool]:
    """List available GAP tools."""
    return [
        Tool(
            name="check_group_property",
            description=(
                "Check if a group satisfies a specific property. "
                "Useful for verifying if groups have certain characteristics. "
                "Properties include: abelian, cyclic, simple, solvable, nilpotent, "
                "perfect, supersolvable, p-group (for prime p). "
                "Examples: check if S_4 is abelian, check if D_5 is cyclic."
            ),
            inputSchema={
                "type": "object",
                "properties": {
                    "group": {
                        "type": "string",
                        "description": (
                            "Group description. Examples: 'SymmetricGroup(4)', "
                            "'CyclicGroup(12)', 'DihedralGroup(5)', 'AlternatingGroup(5)', "
                            "'SmallGroup(24, 3)' (3rd group of order 24)"
                        ),
                    },
                    "property": {
                        "type": "string",
                        "description": (
                            "Property to check. Options: abelian, cyclic, simple, solvable, "
                            "nilpotent, perfect, supersolvable, pgroup"
                        ),
                    },
                },
                "required": ["group", "property"],
            },
        ),
        Tool(
            name="find_counterexample",
            description=(
                "Search for a counterexample to a conjecture about groups. "
                "Tests the conjecture on various small groups and returns the first "
                "counterexample found. Very useful for disproving false conjectures. "
                "Example: Find a non-abelian group, find a group that is solvable but not nilpotent."
            ),
            inputSchema={
                "type": "object",
                "properties": {
                    "property": {
                        "type": "string",
                        "description": (
                            "Property that should be false (to find counterexample). "
                            "Options: abelian, cyclic, simple, solvable, nilpotent, perfect"
                        ),
                    },
                    "max_order": {
                        "type": "integer",
                        "description": "Maximum group order to search (default: 100)",
                        "default": 100,
                    },
                    "additional_condition": {
                        "type": "string",
                        "description": (
                            "Optional additional property that must be true. "
                            "Example: 'solvable' to find solvable non-abelian groups"
                        ),
                    },
                },
                "required": ["property"],
            },
        ),
        Tool(
            name="compute_group_invariants",
            description=(
                "Compute important invariants and properties of a group. "
                "Returns order, center order, derived subgroup order, whether it's abelian/cyclic/simple/solvable, "
                "and other structural information. Great for understanding group structure."
            ),
            inputSchema={
                "type": "object",
                "properties": {
                    "group": {
                        "type": "string",
                        "description": (
                            "Group description. Examples: 'SymmetricGroup(5)', "
                            "'SmallGroup(12, 4)'"
                        ),
                    },
                },
                "required": ["group"],
            },
        ),
        Tool(
            name="test_conjecture_on_small_groups",
            description=(
                "Test a conjecture on all groups of small order. "
                "Returns statistics about which groups satisfy the property and lists counterexamples. "
                "Excellent for exploring patterns and testing mathematical conjectures."
            ),
            inputSchema={
                "type": "object",
                "properties": {
                    "property": {
                        "type": "string",
                        "description": (
                            "Property to test. Options: abelian, cyclic, simple, solvable, nilpotent"
                        ),
                    },
                    "max_order": {
                        "type": "integer",
                        "description": "Maximum group order to test (default: 30)",
                        "default": 30,
                    },
                },
                "required": ["property"],
            },
        ),
        Tool(
            name="search_small_groups",
            description=(
                "Search the SmallGroups library for groups matching specific criteria. "
                "GAP has all groups up to order 2000 (except 1024). "
                "Example: Find all groups of order 12, find all abelian groups of order 20."
            ),
            inputSchema={
                "type": "object",
                "properties": {
                    "order": {
                        "type": "integer",
                        "description": "Order of groups to search (must be ≤ 2000, not 1024)",
                    },
                    "property": {
                        "type": "string",
                        "description": (
                            "Optional property filter: abelian, cyclic, simple, solvable, nilpotent"
                        ),
                    },
                },
                "required": ["order"],
            },
        ),
        Tool(
            name="compare_groups",
            description=(
                "Compare two groups by checking if they are isomorphic and listing their properties. "
                "Useful for understanding relationships between different group constructions."
            ),
            inputSchema={
                "type": "object",
                "properties": {
                    "group1": {
                        "type": "string",
                        "description": "First group description",
                    },
                    "group2": {
                        "type": "string",
                        "description": "Second group description",
                    },
                },
                "required": ["group1", "group2"],
            },
        ),
        Tool(
            name="evaluate_gap",
            description=(
                "Evaluate raw GAP code. Use this for advanced operations not covered by other tools. "
                "Requires knowledge of GAP syntax. Example: 'Size(Centre(SymmetricGroup(4)))'"
            ),
            inputSchema={
                "type": "object",
                "properties": {
                    "code": {
                        "type": "string",
                        "description": "GAP code to evaluate",
                    },
                    "timeout": {
                        "type": "integer",
                        "description": "Timeout in seconds (default: 30)",
                        "default": 30,
                    },
                },
                "required": ["code"],
            },
        ),
        Tool(
            name="query_gap",
            description=(
                "Answer questions about group theory in plain English. "
                "This tool automatically generates and executes GAP code to answer your question. "
                "NO GAP knowledge required! Examples: "
                "'What is the order of the center of the alternating group A_5?', "
                "'How many non-abelian groups of order 16 exist?', "
                "'Is the quaternion group Q_8 nilpotent?', "
                "'Find the derived subgroup of the symmetric group S_5'"
            ),
            inputSchema={
                "type": "object",
                "properties": {
                    "question": {
                        "type": "string",
                        "description": "Natural language question about groups"
                    },
                },
                "required": ["question"],
            },
        ),
    ]


def format_result(success: bool, data: Any = None, error: str = None) -> str:
    """Format tool result as JSON."""
    result = {"success": success}
    if data is not None:
        result["data"] = data
    if error is not None:
        result["error"] = error
    return json.dumps(result, indent=2)


def get_gap_property_function(property_name: str) -> str:
    """Map friendly property names to GAP functions."""
    property_map = {
        "abelian": "IsAbelian",
        "cyclic": "IsCyclic",
        "simple": "IsSimple",
        "solvable": "IsSolvable",
        "nilpotent": "IsNilpotent",
        "perfect": "IsPerfect",
        "supersolvable": "IsSupersolvable",
        "pgroup": "IsPGroup",
    }
    return property_map.get(property_name.lower(), None)


@app.call_tool()
async def call_tool(name: str, arguments: dict) -> list[TextContent]:
    """Handle tool calls."""
    try:
        if name == "check_group_property":
            group = arguments["group"]
            property_name = arguments["property"].lower()

            gap_func = get_gap_property_function(property_name)
            if not gap_func:
                return [TextContent(
                    type="text",
                    text=format_result(False, error=f"Unknown property: {property_name}")
                )]

            result = gap.eval(f"{gap_func}({group})")

            if not result.success:
                return [TextContent(
                    type="text",
                    text=format_result(False, error=result.error or "GAP evaluation failed")
                )]

            return [TextContent(
                type="text",
                text=format_result(True, {
                    "group": group,
                    "property": property_name,
                    "result": result.value,
                    "explanation": f"The group {group} is {'NOT ' if not result.value else ''}{property_name}"
                })
            )]

        elif name == "find_counterexample":
            property_name = arguments["property"].lower()
            max_order = arguments.get("max_order", 100)
            additional_condition = arguments.get("additional_condition", "").lower()

            # Ensure SmallGrp is loaded
            if not ensure_smallgrp():
                return [TextContent(
                    type="text",
                    text=format_result(False, error="SmallGrp package could not be loaded")
                )]

            gap_func = get_gap_property_function(property_name)
            if not gap_func:
                return [TextContent(
                    type="text",
                    text=format_result(False, error=f"Unknown property: {property_name}")
                )]

            additional_func = None
            if additional_condition:
                additional_func = get_gap_property_function(additional_condition)
                if not additional_func:
                    return [TextContent(
                        type="text",
                        text=format_result(False, error=f"Unknown additional condition: {additional_condition}")
                    )]

            # Search through small groups
            counterexamples = []
            for order in range(1, min(max_order + 1, 101)):
                if order == 1:
                    continue

                # Get number of groups of this order
                num_groups_result = gap.eval(f"NrSmallGroups({order})")
                if not num_groups_result.success:
                    continue

                num_groups = num_groups_result.value
                if not isinstance(num_groups, int):
                    continue

                for idx in range(1, min(num_groups + 1, 20)):  # Limit to first 20 of each order
                    group_expr = f"SmallGroup({order}, {idx})"

                    # Check additional condition if specified
                    if additional_func:
                        additional_result = gap.eval(f"{additional_func}({group_expr})")
                        if not additional_result.success or not additional_result.value:
                            continue

                    # Check main property
                    result = gap.eval(f"{gap_func}({group_expr})")
                    if result.success and not result.value:
                        # Found counterexample!
                        counterexamples.append({
                            "group": group_expr,
                            "order": order,
                            "index": idx,
                        })
                        if len(counterexamples) >= 3:  # Return first 3
                            break

                if len(counterexamples) >= 3:
                    break

            if counterexamples:
                return [TextContent(
                    type="text",
                    text=format_result(True, {
                        "counterexamples": counterexamples,
                        "explanation": f"Found {len(counterexamples)} group(s) that are NOT {property_name}"
                        + (f" but ARE {additional_condition}" if additional_condition else "")
                    })
                )]
            else:
                return [TextContent(
                    type="text",
                    text=format_result(True, {
                        "counterexamples": [],
                        "explanation": f"No counterexamples found up to order {max_order}"
                    })
                )]

        elif name == "compute_group_invariants":
            group = arguments["group"]

            # Compute various invariants
            invariants = {}

            # Order
            order_result = gap.eval(f"Size({group})")
            if order_result.success:
                invariants["order"] = order_result.value

            # Center order
            center_result = gap.eval(f"Size(Centre({group}))")
            if center_result.success:
                invariants["center_order"] = center_result.value

            # Derived subgroup order
            derived_result = gap.eval(f"Size(DerivedSubgroup({group}))")
            if derived_result.success:
                invariants["derived_subgroup_order"] = derived_result.value

            # Properties
            properties = {}
            for prop_name in ["abelian", "cyclic", "simple", "solvable", "nilpotent", "perfect"]:
                gap_func = get_gap_property_function(prop_name)
                result = gap.eval(f"{gap_func}({group})")
                if result.success:
                    properties[prop_name] = result.value

            invariants["properties"] = properties

            # Number of conjugacy classes
            conj_result = gap.eval(f"Length(ConjugacyClasses({group}))")
            if conj_result.success:
                invariants["num_conjugacy_classes"] = conj_result.value

            return [TextContent(
                type="text",
                text=format_result(True, {
                    "group": group,
                    "invariants": invariants
                })
            )]

        elif name == "test_conjecture_on_small_groups":
            property_name = arguments["property"].lower()
            max_order = arguments.get("max_order", 30)

            # Ensure SmallGrp is loaded
            if not ensure_smallgrp():
                return [TextContent(
                    type="text",
                    text=format_result(False, error="SmallGrp package could not be loaded")
                )]

            gap_func = get_gap_property_function(property_name)
            if not gap_func:
                return [TextContent(
                    type="text",
                    text=format_result(False, error=f"Unknown property: {property_name}")
                )]

            stats = {
                "total_tested": 0,
                "satisfies_property": 0,
                "fails_property": 0,
                "examples_satisfying": [],
                "examples_failing": [],
            }

            for order in range(1, min(max_order + 1, 51)):
                if order == 1:
                    continue

                num_groups_result = gap.eval(f"NrSmallGroups({order})")
                if not num_groups_result.success:
                    continue

                num_groups = num_groups_result.value
                if not isinstance(num_groups, int):
                    continue

                for idx in range(1, min(num_groups + 1, 10)):
                    group_expr = f"SmallGroup({order}, {idx})"
                    result = gap.eval(f"{gap_func}({group_expr})")

                    if result.success:
                        stats["total_tested"] += 1
                        if result.value:
                            stats["satisfies_property"] += 1
                            if len(stats["examples_satisfying"]) < 5:
                                stats["examples_satisfying"].append({"group": group_expr, "order": order})
                        else:
                            stats["fails_property"] += 1
                            if len(stats["examples_failing"]) < 5:
                                stats["examples_failing"].append({"group": group_expr, "order": order})

            return [TextContent(
                type="text",
                text=format_result(True, {
                    "property": property_name,
                    "statistics": stats,
                    "percentage_satisfying": round(
                        100 * stats["satisfies_property"] / stats["total_tested"], 1
                    ) if stats["total_tested"] > 0 else 0
                })
            )]

        elif name == "search_small_groups":
            order = arguments["order"]
            property_filter = arguments.get("property", "").lower()

            # Ensure SmallGrp is loaded
            if not ensure_smallgrp():
                return [TextContent(
                    type="text",
                    text=format_result(False, error="SmallGrp package could not be loaded")
                )]

            if order > 2000 or order == 1024:
                return [TextContent(
                    type="text",
                    text=format_result(False, error="Order must be ≤ 2000 and not 1024")
                )]

            # Get number of groups
            num_result = gap.eval(f"NrSmallGroups({order})")
            if not num_result.success:
                return [TextContent(
                    type="text",
                    text=format_result(False, error="Failed to query SmallGroups library")
                )]

            num_groups = num_result.value

            results = {
                "order": order,
                "total_groups": num_groups,
                "groups": []
            }

            # If property filter, find matching groups
            if property_filter:
                gap_func = get_gap_property_function(property_filter)
                if not gap_func:
                    return [TextContent(
                        type="text",
                        text=format_result(False, error=f"Unknown property: {property_filter}")
                    )]

                for idx in range(1, min(num_groups + 1, 100)):
                    group_expr = f"SmallGroup({order}, {idx})"
                    result = gap.eval(f"{gap_func}({group_expr})")
                    if result.success and result.value:
                        results["groups"].append({"index": idx, "group": group_expr})
            else:
                # Just list all groups (up to 20)
                for idx in range(1, min(num_groups + 1, 20)):
                    results["groups"].append({
                        "index": idx,
                        "group": f"SmallGroup({order}, {idx})"
                    })
                if num_groups > 20:
                    results["note"] = f"Showing first 20 of {num_groups} groups"

            return [TextContent(
                type="text",
                text=format_result(True, results)
            )]

        elif name == "compare_groups":
            group1 = arguments["group1"]
            group2 = arguments["group2"]

            # Check isomorphism
            iso_result = gap.eval(f"IsomorphismGroups({group1}, {group2})")
            are_isomorphic = iso_result.success and iso_result.raw_output != "fail"

            # Get properties of both
            comparison = {
                "group1": group1,
                "group2": group2,
                "are_isomorphic": are_isomorphic,
                "properties": {}
            }

            for prop in ["order", "abelian", "cyclic", "simple", "solvable"]:
                if prop == "order":
                    r1 = gap.eval(f"Size({group1})")
                    r2 = gap.eval(f"Size({group2})")
                else:
                    gap_func = get_gap_property_function(prop)
                    r1 = gap.eval(f"{gap_func}({group1})")
                    r2 = gap.eval(f"{gap_func}({group2})")

                if r1.success and r2.success:
                    comparison["properties"][prop] = {
                        "group1": r1.value,
                        "group2": r2.value,
                        "same": r1.value == r2.value
                    }

            return [TextContent(
                type="text",
                text=format_result(True, comparison)
            )]

        elif name == "evaluate_gap":
            code = arguments["code"]
            timeout = arguments.get("timeout", 30)

            result = gap.eval(code, timeout=timeout)

            if not result.success:
                return [TextContent(
                    type="text",
                    text=format_result(False, error=result.error or "GAP evaluation failed")
                )]

            return [TextContent(
                type="text",
                text=format_result(True, {
                    "code": code,
                    "result": result.value,
                    "raw_output": result.raw_output
                })
            )]

        elif name == "query_gap":
            question = arguments["question"]

            # Use the query agent to generate and execute GAP code
            result = query_agent.query(question)

            if not result.success:
                return [TextContent(
                    type="text",
                    text=format_result(False, error=result.error or "Query failed", data={
                        "question": question,
                        "attempted_code": result.final_code,
                        "attempts": result.attempts
                    })
                )]

            return [TextContent(
                type="text",
                text=format_result(True, {
                    "question": question,
                    "answer": result.result_value,
                    "gap_code": result.final_code,
                    "raw_output": result.result_raw,
                    "explanation": result.explanation,
                    "attempts": result.attempts
                })
            )]

        else:
            return [TextContent(
                type="text",
                text=format_result(False, error=f"Unknown tool: {name}")
            )]

    except Exception as e:
        return [TextContent(
            type="text",
            text=format_result(False, error=f"Error: {str(e)}")
        )]


async def main():
    """Run the MCP server."""
    async with stdio_server() as (read_stream, write_stream):
        await app.run(read_stream, write_stream, app.create_initialization_options())


if __name__ == "__main__":
    asyncio.run(main())
