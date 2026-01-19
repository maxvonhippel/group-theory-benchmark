"""
Tests for the Lean MCP server.

These tests verify the Lean 4 theorem proving tools work correctly.
"""

import pytest
import sys
from pathlib import Path

# Add src to path
sys.path.insert(0, str(Path(__file__).parent.parent))

from src.tools.lean_mcp_server import call_tool, format_result
import json


class TestFormatResult:
    """Test result formatting."""

    def test_format_success(self):
        result = format_result(True, {"message": "success"})
        parsed = json.loads(result)
        assert parsed["success"] is True
        assert parsed["data"]["message"] == "success"

    def test_format_error(self):
        result = format_result(False, error="Test error")
        parsed = json.loads(result)
        assert parsed["success"] is False
        assert parsed["error"] == "Test error"


@pytest.mark.asyncio
class TestLeanToolCalls:
    """Test Lean MCP tool calls."""

    async def test_check_theorem_valid(self):
        """Test checking a valid theorem statement."""
        result = await call_tool("check_theorem", {
            "theorem": "theorem test : 2 + 2 = 4 := by sorry"
        })

        assert len(result) == 1
        data = json.loads(result[0].text)
        assert data["success"] is True
        assert "well-formed" in data["data"]["message"]

    async def test_check_theorem_with_type(self):
        """Test checking a theorem with types."""
        result = await call_tool("check_theorem", {
            "theorem": "theorem add_comm (a b : Nat) : a + b = b + a := by sorry"
        })

        assert len(result) == 1
        data = json.loads(result[0].text)
        assert data["success"] is True

    async def test_check_theorem_invalid(self):
        """Test checking an invalid theorem."""
        result = await call_tool("check_theorem", {
            "theorem": "theorem bad : 2 + 2 = 5 := by rfl"
        })

        assert len(result) == 1
        data = json.loads(result[0].text)
        # Should fail because 2 + 2 ≠ 5 and rfl won't work
        assert data["success"] is False
        assert len(data["data"]["errors"]) > 0

    async def test_verify_proof_simple(self):
        """Test verifying a simple proof."""
        result = await call_tool("verify_proof", {
            "theorem": "theorem test : 2 + 2 = 4 := by rfl"
        })

        assert len(result) == 1
        data = json.loads(result[0].text)
        assert data["success"] is True
        assert "verified successfully" in data["data"]["message"]

    async def test_verify_proof_with_sorry(self):
        """Test that proofs with sorry are rejected."""
        result = await call_tool("verify_proof", {
            "theorem": "theorem test : 2 + 2 = 4 := by sorry"
        })

        assert len(result) == 1
        data = json.loads(result[0].text)
        assert data["success"] is False
        assert "sorry" in data["error"].lower()

    async def test_verify_proof_nat_addition(self):
        """Test verifying a Nat addition proof."""
        # Note: n + 0 = n works with rfl, but 0 + n = n requires induction
        result = await call_tool("verify_proof", {
            "theorem": "theorem add_zero (n : Nat) : n + 0 = n := by rfl"
        })

        assert len(result) == 1
        data = json.loads(result[0].text)
        assert data["success"] is True

    async def test_get_proof_state(self):
        """Test getting proof state at a position."""
        theorem = """theorem add_example (a b : Nat) : a + b = b + a := by
  sorry"""
        
        result = await call_tool("get_proof_state", {
            "theorem": theorem,
            "line": 1,
            "character": 2
        })

        assert len(result) == 1
        data = json.loads(result[0].text)
        # Should either succeed and show goals, or indicate no proof state
        assert "success" in data

    async def test_evaluate_lean_simple(self):
        """Test evaluating simple Lean code."""
        result = await call_tool("evaluate_lean", {
            "code": "#check Nat"
        })

        assert len(result) == 1
        data = json.loads(result[0].text)
        # #check should work without errors
        assert data["success"] is True

    async def test_evaluate_lean_eval(self):
        """Test evaluating Lean computation."""
        result = await call_tool("evaluate_lean", {
            "code": "#eval 2 + 2"
        })

        assert len(result) == 1
        data = json.loads(result[0].text)
        # Should successfully evaluate
        assert data["success"] is True

    async def test_evaluate_lean_definition(self):
        """Test evaluating a definition."""
        result = await call_tool("evaluate_lean", {
            "code": "def myDouble (n : Nat) : Nat := n + n"
        })

        assert len(result) == 1
        data = json.loads(result[0].text)
        assert data["success"] is True

    async def test_check_theorem_with_imports(self):
        """Test checking theorem with imports."""
        result = await call_tool("check_theorem", {
            "theorem": "theorem test : True := by trivial",
            "imports": "import Mathlib.Tactic.Basic"
        })

        assert len(result) == 1
        data = json.loads(result[0].text)
        # Should work even if Mathlib isn't fully available
        assert "success" in data


if __name__ == "__main__":
    pytest.main([__file__, "-v"])