"""
GAP Query Agent - Iteratively generates and executes GAP code from English queries.

This agent:
1. Takes an English query about group theory
2. Generates GAP code using BAML/LLM
3. Executes the code
4. If it fails, iteratively fixes it (up to max_attempts)
5. Returns the final code and result

The agent preserves conversation history so it doesn't repeat mistakes.
"""

from dataclasses import dataclass
from typing import Optional
import sys
from pathlib import Path

# Add src to path for imports
sys.path.insert(0, str(Path(__file__).parent.parent))

from src.tools.gap import Gap, GapResult
from baml_client.baml_client.sync_client import b


@dataclass
class GAPQueryResult:
    """Result from GAP query agent."""
    success: bool
    query: str
    final_code: str
    result_value: any
    result_raw: str
    explanation: str
    attempts: int
    error: Optional[str] = None


class GAPQueryAgent:
    """
    Agent that translates English queries to GAP code and executes them.

    Uses BAML/LLM to generate code and iteratively fixes errors until
    successful or max attempts reached.
    """

    def __init__(self, max_attempts: int = 5):
        """
        Initialize the agent.

        Args:
            max_attempts: Maximum number of fix attempts before giving up
        """
        self.gap = Gap()
        self.max_attempts = max_attempts

    def query(self, question: str) -> GAPQueryResult:
        """
        Answer a question about group theory by generating and executing GAP code.

        Args:
            question: English language question about groups

        Returns:
            GAPQueryResult with the answer and execution details
        """
        # Track attempt history to avoid repeating mistakes
        previous_attempts = []

        # Step 1: Generate initial GAP code
        try:
            gap_code = b.GenerateGAPCode(question)
            current_code = gap_code.code
            explanation = gap_code.explanation
        except Exception as e:
            return GAPQueryResult(
                success=False,
                query=question,
                final_code="",
                result_value=None,
                result_raw="",
                explanation="",
                attempts=0,
                error=f"Failed to generate GAP code: {str(e)}"
            )

        # Step 2: Try to execute, fix if needed
        for attempt in range(self.max_attempts):
            # Execute the code
            result = self.gap.eval(current_code)

            if result.success and not self._is_error_output(result.raw_output):
                # Success!
                return GAPQueryResult(
                    success=True,
                    query=question,
                    final_code=current_code,
                    result_value=result.value,
                    result_raw=result.raw_output,
                    explanation=explanation,
                    attempts=attempt + 1
                )

            # Failed - need to fix
            if attempt == self.max_attempts - 1:
                # Last attempt failed, give up
                return GAPQueryResult(
                    success=False,
                    query=question,
                    final_code=current_code,
                    result_value=None,
                    result_raw=result.raw_output if result.raw_output else "",
                    explanation=explanation,
                    attempts=attempt + 1,
                    error=result.error or f"Execution failed: {result.raw_output}"
                )

            # Try to fix the code
            error_message = result.error if result.error else result.raw_output
            previous_attempts.append(current_code)

            try:
                fix = b.FixGAPCode(
                    original_code=current_code,
                    error_message=error_message,
                    previous_attempts=previous_attempts
                )
                current_code = fix.fixed_code
                # Update explanation with fix reasoning
                explanation += f"\n[Fix attempt {attempt + 1}]: {fix.reasoning}"
            except Exception as e:
                return GAPQueryResult(
                    success=False,
                    query=question,
                    final_code=current_code,
                    result_value=None,
                    result_raw="",
                    explanation=explanation,
                    attempts=attempt + 1,
                    error=f"Failed to generate fix: {str(e)}"
                )

        # Should never reach here
        return GAPQueryResult(
            success=False,
            query=question,
            final_code=current_code,
            result_value=None,
            result_raw="",
            explanation=explanation,
            attempts=self.max_attempts,
            error="Max attempts reached"
        )

    def _is_error_output(self, output: str) -> bool:
        """Check if output contains error indicators."""
        if not output:
            return False
        error_indicators = [
            "Error,",
            "Syntax error",
            "Variable:",
            "must have a value",
            "fail",
            "brk>",
        ]
        return any(indicator in output for indicator in error_indicators)


# Convenience function
def query_gap(question: str, max_attempts: int = 5) -> GAPQueryResult:
    """
    Convenience function to query GAP with an English question.

    Args:
        question: English language question about groups
        max_attempts: Maximum fix attempts

    Returns:
        GAPQueryResult with answer

    Example:
        >>> result = query_gap("Is the symmetric group S_4 abelian?")
        >>> print(result.result_value)
        False
    """
    agent = GAPQueryAgent(max_attempts=max_attempts)
    return agent.query(question)
