#!/usr/bin/env python3
"""
Test script for the GAP Python interface.

This script demonstrates how to use the Gap class to perform
algebraic computations using the GAP computer algebra system.
"""

from src.tools.gap import Gap, get_gap

def test_basic_arithmetic():
    """Test basic arithmetic operations."""
    print("=" * 60)
    print("Testing Basic Arithmetic")
    print("=" * 60)
    
    gap = Gap()
    
    # Simple arithmetic
    result = gap.eval('2 + 2')
    print(f"2 + 2 = {result.value} (raw: {result.raw_output})")
    
    result = gap.eval('Factorial(10)')
    print(f"Factorial(10) = {result.value}")
    
    result = gap.eval('Gcd(120, 75)')
    print(f"Gcd(120, 75) = {result.value}")
    print()

def test_group_theory():
    """Test group theory operations."""
    print("=" * 60)
    print("Testing Group Theory")
    print("=" * 60)
    
    gap = Gap()
    
    # Symmetric group
    result = gap.symmetric_group(4)
    print(f"Symmetric Group S_4: {result.raw_output}")
    
    # Group order
    result = gap.group_order('SymmetricGroup(5)')
    print(f"Order of S_5: {result.value}")
    
    # Check if abelian
    result = gap.is_abelian('SymmetricGroup(3)')
    print(f"Is S_3 abelian? {result.raw_output}")
    
    result = gap.is_abelian('CyclicGroup(6)')
    print(f"Is C_6 abelian? {result.raw_output}")
    
    # Cyclic group
    result = gap.is_cyclic('CyclicGroup(12)')
    print(f"Is C_12 cyclic? {result.raw_output}")
    print()

def test_conjugacy_classes():
    """Test conjugacy class computations."""
    print("=" * 60)
    print("Testing Conjugacy Classes")
    print("=" * 60)
    
    gap = Gap()
    
    # Number of conjugacy classes in S_4
    result = gap.eval('Length(ConjugacyClasses(SymmetricGroup(4)))')
    print(f"Number of conjugacy classes in S_4: {result.value}")
    
    # Center of S_3
    result = gap.center('SymmetricGroup(3)')
    print(f"Center of S_3: {result.raw_output}")
    print()

def test_convenience_functions():
    """Test convenience functions."""
    print("=" * 60)
    print("Testing Convenience Functions")
    print("=" * 60)
    
    gap = get_gap()  # Using singleton instance
    
    # Create various groups
    result = gap.dihedral_group(5)
    print(f"Dihedral group D_5: {result.raw_output}")
    
    result = gap.alternating_group(4)
    print(f"Alternating group A_4: {result.raw_output}")
    
    result = gap.group_order('AlternatingGroup(4)')
    print(f"Order of A_4: {result.value}")
    print()

def test_error_handling():
    """Test error handling."""
    print("=" * 60)
    print("Testing Error Handling")
    print("=" * 60)
    
    gap = Gap()
    
    # Invalid syntax
    result = gap.eval('1 / 0')
    print(f"1/0 - Success: {result.success}")
    if not result.success:
        print(f"Error: {result.error}")
    
    # Undefined variable
    result = gap.eval('UndefinedVariable')
    print(f"UndefinedVariable - Success: {result.success}")
    print(f"Output: {result.raw_output}")
    print()

def main():
    """Run all tests."""
    print("\n" + "=" * 60)
    print("GAP Python Interface Test Suite")
    print("=" * 60 + "\n")
    
    try:
        test_basic_arithmetic()
        test_group_theory()
        test_conjugacy_classes()
        test_convenience_functions()
        test_error_handling()
        
        print("=" * 60)
        print("All tests completed!")
        print("=" * 60)
        
    except Exception as e:
        print(f"\nTest failed with error: {e}")
        import traceback
        traceback.print_exc()

if __name__ == "__main__":
    main()