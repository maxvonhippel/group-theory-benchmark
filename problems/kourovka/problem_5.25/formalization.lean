/-
Kourovka Notebook Problem 5.25 (V. M. Kopytov)

Prove that the factor-group of any soluble linearly ordered group by its
derived subgroup is non-periodic.

Key concepts:
- A linearly ordered group is a group G with a total order ≤ such that
  a ≤ b implies ca ≤ cb and ac ≤ bc for all c.
- The derived subgroup G' is the commutator subgroup [G,G].
- A group is non-periodic (or has an element of infinite order) if it
  contains an element g ≠ 1 with g^n ≠ 1 for all n > 0.
- The statement says G/G' is non-periodic, i.e., the abelianization of G
  contains an element of infinite order.
-/

import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.Torsion
import Mathlib.Algebra.Order.Group.Defs

/--
A linearly ordered group (not necessarily commutative) is a group with a
linear order that is compatible with multiplication on both sides.
This is the standard notion for ordered groups that may be non-commutative.
-/
class LinearOrderedGroup (G : Type*) extends Group G, LinearOrder G where
  /-- Left multiplication preserves order -/
  mul_le_mul_left : ∀ a b : G, a ≤ b → ∀ c : G, c * a ≤ c * b
  /-- Right multiplication preserves order -/
  mul_le_mul_right : ∀ a b : G, a ≤ b → ∀ c : G, a * c ≤ b * c

/--
Kourovka Problem 5.25 (V. M. Kopytov):

If G is a soluble (solvable) linearly ordered group, then G/G' (the
abelianization, i.e., the quotient by the derived subgroup) is non-periodic.

Equivalently, the abelianization of any solvable linearly ordered group
contains an element of infinite order.

Note: The abelianization `Abelianization G` is definitionally `G ⧸ commutator G`.
-/
theorem kourovka_5_25
    (G : Type*) [LinearOrderedGroup G] [IsSolvable G] [Nontrivial G] :
    ¬ Monoid.IsTorsion (Abelianization G) := by
  sorry

/--
Alternative formulation: The abelianization contains an element of infinite order.
-/
theorem kourovka_5_25'
    (G : Type*) [LinearOrderedGroup G] [IsSolvable G] [Nontrivial G] :
    ∃ g : Abelianization G, ¬ IsOfFinOrder g := by
  have h := kourovka_5_25 G
  rw [Monoid.not_isTorsion_iff] at h
  exact h
