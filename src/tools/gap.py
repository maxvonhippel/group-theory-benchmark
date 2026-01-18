"""
Python interface to GAP (Groups, Algorithms, Programming) system.

This module provides a clean Python interface to GAP using subprocess mode,
which is reliable and works with any GAP installation.

Example usage:
    >>> from src.tools.gap import Gap
    >>> gap = Gap()
    >>> result = gap.eval('SymmetricGroup(4)')
    >>> size = gap.eval('Size(SymmetricGroup(5))')
    
    Or use convenience methods:
    >>> S4 = gap.symmetric_group(4)
    >>> size = gap.group_order('SymmetricGroup(4)')
"""

import os
import subprocess
from pathlib import Path
from typing import Any, Optional, Union
from dataclasses import dataclass


@dataclass
class GapResult:
    """Result from a GAP computation."""
    value: Any
    raw_output: str
    success: bool
    error: Optional[str] = None


class GapError(Exception):
    """Exception raised when GAP computation fails."""
    pass


class Gap:
    """
    Interface to the GAP computer algebra system.
    
    This class provides methods to evaluate GAP expressions and interact
    with GAP's computational group theory capabilities.
    
    Attributes:
        gap_executable: Path to the GAP executable
    """
    
    def __init__(self, gap_root: Optional[Union[str, Path]] = None):
        """
        Initialize GAP interface.
        
        Args:
            gap_root: Path to GAP installation. If None, uses ./gap or searches PATH
        """
        self.gap_root = self._find_gap_root(gap_root)
        self.gap_executable = self._find_gap_executable()
    
    def _find_gap_root(self, gap_root: Optional[Union[str, Path]]) -> Path:
        """Find the GAP installation directory."""
        if gap_root:
            return Path(gap_root).resolve()
        
        # Try ./gap directory first (from our Makefile setup)
        local_gap = Path(__file__).parent.parent.parent / "gap"
        if local_gap.exists() and (local_gap / "gap").exists():
            return local_gap
        
        # Try to find via gap executable
        try:
            result = subprocess.run(
                ["which", "gap"],
                capture_output=True,
                text=True,
                check=True
            )
            gap_path = Path(result.stdout.strip()).resolve()
            # GAP executable might be in gap/gap or gap/bin/gap
            if gap_path.parent.name == "bin":
                return gap_path.parent.parent
            return gap_path.parent
        except (subprocess.CalledProcessError, FileNotFoundError):
            pass
        
        raise GapError("Could not find GAP installation. Please specify gap_root or install GAP.")
    
    def _find_gap_executable(self) -> Path:
        """Find the GAP executable."""
        # Check for submodule gap build directory first
        submodule_gap_build = Path(__file__).parent.parent.parent / "gap" / "build" / "gap-nocomp"
        if submodule_gap_build.exists() and os.access(submodule_gap_build, os.X_OK):
            return submodule_gap_build
        
        # Check in gap_root
        candidates = [
            self.gap_root / "build" / "gap-nocomp",
            self.gap_root / "gap",
            self.gap_root / "bin" / "gap",
        ]
        
        for candidate in candidates:
            if candidate.exists() and os.access(candidate, os.X_OK):
                return candidate
        
        # Try system PATH
        try:
            result = subprocess.run(
                ["which", "gap"],
                capture_output=True,
                text=True,
                check=True
            )
            return Path(result.stdout.strip())
        except (subprocess.CalledProcessError, FileNotFoundError):
            pass
        
        raise GapError("Could not find GAP executable")
    
    def eval(self, command: str, timeout: Optional[int] = 30) -> GapResult:
        """
        Evaluate a GAP command and return the result.
        
        Args:
            command: GAP command to evaluate
            timeout: Maximum time to wait for result (seconds)
        
        Returns:
            GapResult object containing the result
        
        Raises:
            GapError: If evaluation fails
        
        Examples:
            >>> gap = Gap()
            >>> result = gap.eval('2 + 2')
            >>> result.value
            4
            >>> result = gap.eval('SymmetricGroup(4)')
        """
        # Ensure command ends with semicolon
        if not command.rstrip().endswith(';'):
            command = command.rstrip() + ';'
        
        # Execute command and print result
        script = f"""
_result_ := {command};
if IsBound(_result_) then
    if IsInt(_result_) or IsBool(_result_) or IsString(_result_) then
        Print(_result_);
    else
        Print(ViewString(_result_));
    fi;
fi;
QUIT;
"""
        
        try:
            result = subprocess.run(
                [str(self.gap_executable), "-q", "-A", "-b"],  # -q quiet, -A no auto packages, -b no banner
                input=script,
                capture_output=True,
                text=True,
                timeout=timeout,
                check=False
            )
            
            # Combine stdout and stderr, then filter
            full_output = result.stdout + "\n" + result.stderr
            lines = full_output.split('\n')
            
            # Filter out GAP info messages and error prompts
            filtered_lines = []
            in_error = False
            for line in lines:
                stripped = line.strip()

                # Detect start of error messages
                if 'Error,' in stripped or 'failed to load' in stripped:
                    in_error = True

                # Detect end of error messages (when we see a real result or prompt)
                if in_error and (stripped.startswith('gap>') or (stripped and not any([
                    'Error,' in stripped,
                    'failed' in stripped,
                    'called from' in stripped,
                    stripped.startswith('at /'),
                    stripped.startswith(')'),
                    stripped.startswith('func('),
                    'CallAndInstallPostRestore' in stripped,
                    'package' in stripped.lower(),
                ]))):
                    in_error = False

                # Skip if in error block or matches filter patterns
                if in_error or any([
                    stripped.startswith('#I'),
                    'package is not available' in stripped,
                    'cannot be loaded' in stripped,
                    'you can' in stripped.lower(),
                    'called from' in stripped,
                    'Options stack has been reset' in stripped,
                    'CallAndInstallPostRestore' in stripped,
                    stripped.startswith('at /'),
                    not stripped  # skip empty lines
                ]):
                    continue
                filtered_lines.append(stripped)
            
            # The actual result should be the last non-empty line
            if not filtered_lines:
                return GapResult(
                    value=None,
                    raw_output="",
                    success=False,
                    error="No output from GAP"
                )
            
            output = filtered_lines[-1] if filtered_lines else ""
            
            # Try to parse the output
            value = self._parse_gap_output(output)
            
            return GapResult(
                value=value,
                raw_output=output,
                success=True
            )
            
        except subprocess.TimeoutExpired:
            return GapResult(
                value=None,
                raw_output="",
                success=False,
                error=f"Command timed out after {timeout} seconds"
            )
        except Exception as e:
            return GapResult(
                value=None,
                raw_output="",
                success=False,
                error=str(e)
            )
    
    def _parse_gap_output(self, output: str) -> Any:
        """
        Parse GAP output to Python types when possible.
        
        This is a simple parser for common cases. For complex objects,
        the raw output string is returned.
        """
        output = output.strip()
        
        # Handle empty output
        if not output:
            return None
        
        # Try to parse as integer
        try:
            return int(output)
        except ValueError:
            pass
        
        # Try to parse as boolean
        if output == 'true':
            return True
        elif output == 'false':
            return False
        
        # Return as string for everything else
        return output
    
    # Convenience methods for common algebraic operations
    
    def symmetric_group(self, n: int) -> GapResult:
        """Create the symmetric group S_n."""
        return self.eval(f'SymmetricGroup({n})')
    
    def cyclic_group(self, n: int) -> GapResult:
        """Create the cyclic group C_n."""
        return self.eval(f'CyclicGroup({n})')
    
    def dihedral_group(self, n: int) -> GapResult:
        """Create the dihedral group D_n."""
        return self.eval(f'DihedralGroup({n})')
    
    def alternating_group(self, n: int) -> GapResult:
        """Create the alternating group A_n."""
        return self.eval(f'AlternatingGroup({n})')
    
    def group_order(self, group_expr: str) -> GapResult:
        """Get the order (size) of a group."""
        return self.eval(f'Size({group_expr})')
    
    def is_abelian(self, group_expr: str) -> GapResult:
        """Check if a group is abelian."""
        return self.eval(f'IsAbelian({group_expr})')
    
    def is_cyclic(self, group_expr: str) -> GapResult:
        """Check if a group is cyclic."""
        return self.eval(f'IsCyclic({group_expr})')
    
    def center(self, group_expr: str) -> GapResult:
        """Get the center of a group."""
        return self.eval(f'Center({group_expr})')
    
    def subgroups(self, group_expr: str) -> GapResult:
        """Get all subgroups of a group."""
        return self.eval(f'AllSubgroups({group_expr})')
    
    def normal_subgroups(self, group_expr: str) -> GapResult:
        """Get all normal subgroups of a group."""
        return self.eval(f'NormalSubgroups({group_expr})')
    
    def conjugacy_classes(self, group_expr: str) -> GapResult:
        """Get conjugacy classes of a group."""
        return self.eval(f'ConjugacyClasses({group_expr})')
    
    def character_table(self, group_expr: str) -> GapResult:
        """Get the character table of a group."""
        return self.eval(f'CharacterTable({group_expr})')
    
    def __enter__(self):
        """Context manager support."""
        return self
    
    def __exit__(self, exc_type, exc_val, exc_tb):
        """Cleanup on context exit."""
        return False
    
    def __repr__(self) -> str:
        """String representation."""
        return f"Gap(gap_root={self.gap_root}, backend=subprocess)"


# Convenience instance for simple usage
_default_gap: Optional[Gap] = None

def get_gap() -> Gap:
    """Get the default GAP instance (singleton)."""
    global _default_gap
    if _default_gap is None:
        _default_gap = Gap()
    return _default_gap