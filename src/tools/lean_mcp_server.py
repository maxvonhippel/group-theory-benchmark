"""
Lean MCP Server - Model Context Protocol server for Lean 4 theorem prover.

This MCP server provides tools for formal mathematical proof verification
using Lean 4. It's designed for AI agents to explore formal mathematics,
verify theorems, and check proofs without requiring detailed knowledge of Lean syntax.
"""

import asyncio
import json
import tempfile
from pathlib import Path
from typing import Any, Optional
from mcp.server import Server
from mcp.server.stdio import stdio_server
from mcp.types import Tool, TextContent

from leanclient import LeanLSPClient


# Initialize MCP server
app = Server("lean-server")

# Global Lean client (initialized lazily)
_lean_client: Optional[LeanLSPClient] = None
_scratch_project_path: Optional[Path] = None


def get_lean_client() -> LeanLSPClient:
    """Get or create the Lean LSP client."""
    global _lean_client, _scratch_project_path
    
    if _lean_client is None:
        # Use the scratch project directory
        scratch_path = Path(__file__).parent.parent.parent / "lean_scratch"
        if not scratch_path.exists():
            raise RuntimeError(
                "Lean scratch project not found. Run 'make setup' first."
            )
        
        _scratch_project_path = scratch_path
        # Initialize with initial_build=False to speed up startup
        _lean_client = LeanLSPClient(
            project_path=str(_scratch_project_path),
            max_opened_files=4,
            initial_build=False,
            prevent_cache_get=True  # Skip cache downloads for faster testing
        )
    
    return _lean_client


@app.list_tools()
async def list_tools() -> list[Tool]:
    """List available Lean tools."""
    return [
        Tool(
            name="check_theorem",
            description=(
                "Check if a Lean theorem statement is valid and type-checks. "
                "Does NOT prove the theorem, just verifies the statement is well-formed. "
                "Example: Check if 'theorem example : 2 + 2 = 4 := by sorry' is a valid statement."
            ),
            inputSchema={
                "type": "object",
                "properties": {
                    "theorem": {
                        "type": "string",
                        "description": (
                            "Lean theorem statement to check. "
                            "Can use 'sorry' or 'admit' for unproven parts. "
                            "Example: 'theorem add_comm (a b : Nat) : a + b = b + a := by sorry'"
                        ),
                    },
                    "imports": {
                        "type": "string",
                        "description": (
                            "Optional imports to include. "
                            "Example: 'import Mathlib.Data.Nat.Basic'"
                        ),
                    },
                },
                "required": ["theorem"],
            },
        ),
        Tool(
            name="verify_proof",
            description=(
                "Verify a complete Lean proof. Returns success if proof is valid, "
                "errors if proof has gaps or mistakes. "
                "Example: Verify that a proof of '2 + 2 = 4' is correct."
            ),
            inputSchema={
                "type": "object",
                "properties": {
                    "theorem": {
                        "type": "string",
                        "description": "Complete Lean theorem with proof",
                    },
                    "imports": {
                        "type": "string",
                        "description": "Optional imports to include",
                    },
                },
                "required": ["theorem"],
            },
        ),
        Tool(
            name="get_proof_state",
            description=(
                "Get the current proof state (goals) at a specific point in a proof. "
                "Useful for understanding what needs to be proved at each step. "
                "Returns tactic state showing hypotheses and goals."
            ),
            inputSchema={
                "type": "object",
                "properties": {
                    "theorem": {
                        "type": "string",
                        "description": "Lean theorem with partial proof",
                    },
                    "line": {
                        "type": "integer",
                        "description": "Line number to check (0-indexed)",
                    },
                    "character": {
                        "type": "integer",
                        "description": "Character position on line (0-indexed)",
                        "default": 0,
                    },
                    "imports": {
                        "type": "string",
                        "description": "Optional imports to include",
                    },
                },
                "required": ["theorem", "line"],
            },
        ),
        Tool(
            name="evaluate_lean",
            description=(
                "Evaluate arbitrary Lean code. Use for advanced operations "
                "or when other tools don't fit your needs. "
                "Example: '#eval 2 + 2' or 'def myFunc := ...' "
            ),
            inputSchema={
                "type": "object",
                "properties": {
                    "code": {
                        "type": "string",
                        "description": "Lean code to evaluate",
                    },
                    "imports": {
                        "type": "string",
                        "description": "Optional imports to include",
                    },
                },
                "required": ["code"],
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


async def check_lean_code(code: str, imports: str = "") -> dict:
    """
    Check Lean code by creating a temporary file and getting diagnostics.
    Returns diagnostics and any errors found.
    """
    client = get_lean_client()
    
    # Create full content with imports
    full_content = f"{imports}\n\n{code}" if imports else code
    
    # Create temporary file in the scratch project
    temp_file = _scratch_project_path / "LeanScratch" / "Temp.lean"
    temp_file.parent.mkdir(parents=True, exist_ok=True)
    
    try:
        # Write content
        temp_file.write_text(full_content)
        
        # Get relative path for client
        rel_path = "LeanScratch/Temp.lean"
        
        # Open and get diagnostics
        client.open_file(rel_path, dependency_build_mode="never")
        diagnostics = client.get_diagnostics(rel_path, inactivity_timeout=5.0)
        
        # Close file
        client.close_file(rel_path, blocking=True)
        
        # Parse diagnostics
        errors = []
        warnings = []
        
        for diag in diagnostics.diagnostics:
            severity = diag.get("severity", 1)
            message = diag.get("message", "")
            range_info = diag.get("range", {})
            
            diag_info = {
                "message": message,
                "line": range_info.get("start", {}).get("line", 0),
                "character": range_info.get("start", {}).get("character", 0),
            }
            
            if severity == 1:  # Error
                errors.append(diag_info)
            elif severity == 2:  # Warning
                warnings.append(diag_info)
        
        return {
            "success": len(errors) == 0,
            "errors": errors,
            "warnings": warnings,
            "diagnostics": diagnostics.diagnostics,
        }
    
    finally:
        # Clean up
        if temp_file.exists():
            temp_file.unlink()


@app.call_tool()
async def call_tool(name: str, arguments: dict) -> list[TextContent]:
    """Handle tool calls."""
    try:
        if name == "check_theorem":
            theorem = arguments["theorem"]
            imports = arguments.get("imports", "")
            
            result = await check_lean_code(theorem, imports)
            
            if result["success"]:
                return [TextContent(
                    type="text",
                    text=format_result(True, {
                        "message": "Theorem statement is well-formed",
                        "warnings": result["warnings"],
                    })
                )]
            else:
                return [TextContent(
                    type="text",
                    text=format_result(False, {
                        "errors": result["errors"],
                        "warnings": result["warnings"],
                    }, error="Theorem has errors")
                )]
        
        elif name == "verify_proof":
            theorem = arguments["theorem"]
            imports = arguments.get("imports", "")
            
            result = await check_lean_code(theorem, imports)
            
            # For proof verification, we need zero errors and no 'sorry' or 'admit'
            has_sorry = "sorry" in theorem.lower() or "admit" in theorem.lower()
            
            if result["success"] and not has_sorry:
                return [TextContent(
                    type="text",
                    text=format_result(True, {
                        "message": "Proof verified successfully",
                        "warnings": result["warnings"],
                    })
                )]
            elif has_sorry:
                return [TextContent(
                    type="text",
                    text=format_result(False, error="Proof contains 'sorry' or 'admit' - proof incomplete")
                )]
            else:
                return [TextContent(
                    type="text",
                    text=format_result(False, {
                        "errors": result["errors"],
                        "warnings": result["warnings"],
                    }, error="Proof verification failed")
                )]
        
        elif name == "get_proof_state":
            theorem = arguments["theorem"]
            line = arguments["line"]
            character = arguments.get("character", 0)
            imports = arguments.get("imports", "")
            
            client = get_lean_client()
            
            # Create full content
            full_content = f"{imports}\n\n{theorem}" if imports else theorem
            
            # Adjust line number if we added imports
            if imports:
                line += len(imports.split("\n")) + 2
            
            # Create temporary file
            temp_file = _scratch_project_path / "LeanScratch" / "Temp.lean"
            temp_file.parent.mkdir(parents=True, exist_ok=True)
            
            try:
                temp_file.write_text(full_content)
                rel_path = "LeanScratch/Temp.lean"
                
                # Open file and get goal
                client.open_file(rel_path, dependency_build_mode="never")
                
                # Wait for file to be processed
                client.get_diagnostics(rel_path, inactivity_timeout=5.0)
                
                # Get goal at position
                goal = client.get_goal(rel_path, line, character)
                
                # Close file
                client.close_file(rel_path, blocking=True)
                
                if goal:
                    return [TextContent(
                        type="text",
                        text=format_result(True, {
                            "proof_state": goal,
                            "goals": goal.get("goals", []),
                            "rendered": goal.get("rendered", ""),
                        })
                    )]
                else:
                    return [TextContent(
                        type="text",
                        text=format_result(False, error="No proof state at this position")
                    )]
            
            finally:
                if temp_file.exists():
                    temp_file.unlink()
        
        elif name == "evaluate_lean":
            code = arguments["code"]
            imports = arguments.get("imports", "")
            
            result = await check_lean_code(code, imports)
            
            return [TextContent(
                type="text",
                text=format_result(result["success"], {
                    "errors": result["errors"],
                    "warnings": result["warnings"],
                    "diagnostics": result["diagnostics"],
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