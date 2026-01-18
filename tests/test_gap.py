"""Tests for GAP Python interface."""

import pytest
from src.tools.gap import Gap, GapResult, GapError, get_gap


class TestGapBasic:
    """Test basic GAP functionality."""
    
    def test_gap_initialization(self):
        """Test that Gap instance can be created."""
        gap = Gap()
        assert gap is not None
        assert gap.gap_root is not None
    
    def test_simple_arithmetic(self):
        """Test basic arithmetic operations."""
        gap = Gap()
        result = gap.eval('2+2')
        assert result.success
        assert result.value == 4
    
    def test_factorial(self):
        """Test factorial computation."""
        gap = Gap()
        result = gap.eval('Factorial(5)')
        assert result.success
        assert result.value == 120
    
    def test_prime_check(self):
        """Test prime number checking."""
        gap = Gap()
        result = gap.eval('IsPrime(17)')
        assert result.success
        assert result.value is True
    
    def test_gcd(self):
        """Test GCD computation."""
        gap = Gap()
        result = gap.eval('Gcd(120, 75)')
        assert result.success
        assert result.value == 15


class TestGapGroups:
    """Test group theory operations."""
    
    def test_symmetric_group(self):
        """Test symmetric group creation."""
        gap = Gap()
        result = gap.symmetric_group(4)
        assert result.success
        assert 'Sym' in result.raw_output or 'SymmetricGroup' in result.raw_output
    
    def test_group_order(self):
        """Test group order computation."""
        gap = Gap()
        result = gap.group_order('SymmetricGroup(4)')
        assert result.success
        assert result.value == 24
    
    def test_cyclic_group(self):
        """Test cyclic group creation."""
        gap = Gap()
        result = gap.cyclic_group(6)
        assert result.success
    
    def test_is_abelian(self):
        """Test abelian group check."""
        gap = Gap()
        
        # Cyclic groups are abelian
        result = gap.is_abelian('CyclicGroup(6)')
        assert result.success
        assert result.value is True
        
        # S_3 is not abelian
        result = gap.is_abelian('SymmetricGroup(3)')
        assert result.success
        assert result.value is False
    
    def test_is_cyclic(self):
        """Test cyclic group check."""
        gap = Gap()
        result = gap.is_cyclic('CyclicGroup(12)')
        assert result.success
        assert result.value is True


class TestGapConvenience:
    """Test convenience methods."""
    
    def test_dihedral_group(self):
        """Test dihedral group creation."""
        gap = Gap()
        result = gap.dihedral_group(5)
        assert result.success
    
    def test_alternating_group(self):
        """Test alternating group creation."""
        gap = Gap()
        result = gap.alternating_group(4)
        assert result.success
        
        # Check order is correct (|A_4| = 12)
        result = gap.group_order('AlternatingGroup(4)')
        assert result.success
        assert result.value == 12


class TestGapSingleton:
    """Test singleton instance."""
    
    def test_get_gap(self):
        """Test that get_gap returns a Gap instance."""
        gap = get_gap()
        assert gap is not None
        assert isinstance(gap, Gap)
    
    def test_singleton_same_instance(self):
        """Test that get_gap returns the same instance."""
        gap1 = get_gap()
        gap2 = get_gap()
        assert gap1 is gap2


class TestGapBackend:
    """Test backend selection."""
    
    def test_backend_detection(self):
        """Test that backend is detected correctly."""
        gap = Gap()
        # Should always use subprocess for now
        repr_str = repr(gap)
        assert 'Gap(' in repr_str
        assert 'subprocess' in repr_str