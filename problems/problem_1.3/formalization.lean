/-
Kourovka Notebook Problem 1.3 (L. A. Bokut')

(Well-known problem). Can the group ring Z[G] of a torsion-free group G
contain zero divisors?

This is the Kaplansky Zero Divisor Conjecture: the group ring Z[G] of a
torsion-free group G has no zero divisors.
-/

import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.GroupTheory.Torsion

/-- A group is torsion-free if every non-identity element has infinite order -/
def IsTorsionFreeGroup (G : Type*) [Group G] : Prop :=
  ∀ g : G, g ≠ 1 → ∀ n : ℕ, n ≠ 0 → g ^ n ≠ 1

/-- The group ring Z[G] is the monoid algebra of G over Z -/
abbrev GroupRingZ (G : Type*) [Group G] := MonoidAlgebra ℤ G

/-- A ring has zero divisors if there exist non-zero elements whose product is zero -/
def HasZeroDivisors (R : Type*) [Ring R] : Prop :=
  ∃ a b : R, a ≠ 0 ∧ b ≠ 0 ∧ a * b = 0

/--
Kourovka Problem 1.3: The Kaplansky Zero Divisor Conjecture

The conjecture states that for any torsion-free group G,
the group ring Z[G] has no zero divisors.

This is an open problem. The formalization below captures the conjecture statement.
-/
theorem kaplansky_zero_divisor_conjecture
    (G : Type*) [Group G] (hG : IsTorsionFreeGroup G) :
    ¬ HasZeroDivisors (GroupRingZ G) := by
  sorry

/--
Alternative formulation: The group ring Z[G] of a torsion-free group is a domain.

A domain is a non-trivial ring with no zero divisors.
-/
theorem group_ring_is_domain_of_torsion_free
    (G : Type*) [Group G] [Nontrivial G] (hG : IsTorsionFreeGroup G) :
    NoZeroDivisors (GroupRingZ G) := by
  sorry

/--
The problem as an open question: Does there exist a torsion-free group G
such that Z[G] has zero divisors?

A negative answer (this being False) would confirm the Kaplansky conjecture.
A positive answer would provide a counterexample.
-/
def kourovka_1_3_counterexample_exists : Prop :=
  ∃ (G : Type) (_ : Group G), IsTorsionFreeGroup G ∧ HasZeroDivisors (GroupRingZ G)

/-- The Kaplansky conjecture is equivalent to saying no counterexample exists -/
theorem kaplansky_equiv_no_counterexample :
    (∀ (G : Type) [Group G], IsTorsionFreeGroup G → ¬ HasZeroDivisors (GroupRingZ G)) ↔
    ¬ kourovka_1_3_counterexample_exists := by
  constructor
  · intro h ⟨G, hGrp, hTF, hZD⟩
    exact h G hTF hZD
  · intro h G _ hTF hZD
    apply h
    exact ⟨G, inferInstance, hTF, hZD⟩
