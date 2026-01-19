"""
Tests for the GAP MCP server.

These tests verify the high-level abstractions work correctly without
requiring knowledge of GAP syntax.
"""

import pytest
import sys
from pathlib import Path

# Add src to path
sys.path.insert(0, str(Path(__file__).parent.parent))

from src.tools.gap_mcp_server import (
    get_gap_property_function,
    format_result,
    call_tool,
)
import json


class TestPropertyMapping:
    """Test the property name to GAP function mapping."""

    def test_abelian_mapping(self):
        assert get_gap_property_function("abelian") == "IsAbelian"

    def test_cyclic_mapping(self):
        assert get_gap_property_function("cyclic") == "IsCyclic"

    def test_simple_mapping(self):
        assert get_gap_property_function("simple") == "IsSimple"

    def test_unknown_property(self):
        assert get_gap_property_function("unknown") is None


class TestFormatResult:
    """Test result formatting."""

    def test_format_success(self):
        result = format_result(True, {"value": 42})
        parsed = json.loads(result)
        assert parsed["success"] is True
        assert parsed["data"]["value"] == 42

    def test_format_error(self):
        result = format_result(False, error="Test error")
        parsed = json.loads(result)
        assert parsed["success"] is False
        assert parsed["error"] == "Test error"


@pytest.mark.asyncio
class TestToolCalls:
    """Test MCP tool calls."""

    async def test_check_group_property_abelian(self):
        """Test checking if a group is abelian."""
        result = await call_tool("check_group_property", {
            "group": "CyclicGroup(6)",
            "property": "abelian"
        })

        assert len(result) == 1
        data = json.loads(result[0].text)
        assert data["success"] is True
        assert data["data"]["result"] is True
        assert "abelian" in data["data"]["explanation"]

    async def test_check_group_property_non_abelian(self):
        """Test checking if S_3 is abelian (it's not)."""
        result = await call_tool("check_group_property", {
            "group": "SymmetricGroup(3)",
            "property": "abelian"
        })

        assert len(result) == 1
        data = json.loads(result[0].text)
        assert data["success"] is True
        assert data["data"]["result"] is False
        assert "NOT" in data["data"]["explanation"]

    async def test_compute_group_invariants(self):
        """Test computing group invariants."""
        result = await call_tool("compute_group_invariants", {
            "group": "SymmetricGroup(4)"
        })

        assert len(result) == 1
        data = json.loads(result[0].text)
        assert data["success"] is True
        assert data["data"]["invariants"]["order"] == 24
        assert data["data"]["invariants"]["properties"]["abelian"] is False
        assert data["data"]["invariants"]["properties"]["solvable"] is True

    async def test_search_small_groups(self):
        """Test searching small groups library."""
        result = await call_tool("search_small_groups", {
            "order": 6
        })

        assert len(result) == 1
        data = json.loads(result[0].text)
        assert data["success"] is True
        assert data["data"]["order"] == 6
        assert data["data"]["total_groups"] == 2  # C_6 and S_3

    async def test_search_small_groups_with_filter(self):
        """Test searching with property filter."""
        result = await call_tool("search_small_groups", {
            "order": 6,
            "property": "abelian"
        })

        assert len(result) == 1
        data = json.loads(result[0].text)
        assert data["success"] is True
        assert len(data["data"]["groups"]) == 1  # Only C_6 is abelian

    async def test_compare_groups_isomorphic(self):
        """Test comparing isomorphic groups."""
        result = await call_tool("compare_groups", {
            "group1": "CyclicGroup(4)",
            "group2": "SmallGroup(4, 1)"
        })

        assert len(result) == 1
        data = json.loads(result[0].text)
        assert data["success"] is True
        assert data["data"]["are_isomorphic"] is True

    async def test_evaluate_gap_simple(self):
        """Test raw GAP evaluation."""
        result = await call_tool("evaluate_gap", {
            "code": "2 + 2"
        })

        assert len(result) == 1
        data = json.loads(result[0].text)
        assert data["success"] is True
        assert data["data"]["result"] == 4

    async def test_evaluate_gap_group_order(self):
        """Test GAP evaluation with group theory."""
        result = await call_tool("evaluate_gap", {
            "code": "Size(SymmetricGroup(5))"
        })

        assert len(result) == 1
        data = json.loads(result[0].text)
        assert data["success"] is True
        assert data["data"]["result"] == 120

    async def test_find_counterexample(self):
        """Test finding a counterexample."""
        result = await call_tool("find_counterexample", {
            "property": "abelian",
            "max_order": 20
        })

        assert len(result) == 1
        data = json.loads(result[0].text)
        assert data["success"] is True
        assert len(data["data"]["counterexamples"]) > 0
        # S_3 should be among the first counterexamples
        orders = [ex["order"] for ex in data["data"]["counterexamples"]]
        assert 6 in orders  # S_3 has order 6

    async def test_find_counterexample_with_condition(self):
        """Test finding counterexample with additional condition."""
        result = await call_tool("find_counterexample", {
            "property": "nilpotent",
            "additional_condition": "solvable",
            "max_order": 50
        })

        assert len(result) == 1
        data = json.loads(result[0].text)
        assert data["success"] is True
        # Should find solvable but not nilpotent groups

    async def test_test_conjecture_on_small_groups(self):
        """Test conjecture testing."""
        result = await call_tool("test_conjecture_on_small_groups", {
            "property": "cyclic",
            "max_order": 20
        })

        assert len(result) == 1
        data = json.loads(result[0].text)
        assert data["success"] is True
        assert data["data"]["statistics"]["total_tested"] > 0
        assert 0 <= data["data"]["percentage_satisfying"] <= 100

    async def test_query_gap(self):
        """Test natural language query to GAP."""
        result = await call_tool("query_gap", {
            "question": "What is the order of the symmetric group S_4?"
        })

        assert len(result) == 1
        data = json.loads(result[0].text)
        assert data["success"] is True
        assert data["data"]["answer"] == 24
        assert "SymmetricGroup(4)" in data["data"]["gap_code"]

    async def test_query_gap_center(self):
        """Test query about group center."""
        result = await call_tool("query_gap", {
            "question": "What is the order of the center of D_4?"
        })

        assert len(result) == 1
        data = json.loads(result[0].text)
        assert data["success"] is True
        # D_4 (dihedral group of order 8) has center of order 2
        assert data["data"]["answer"] == 2


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
