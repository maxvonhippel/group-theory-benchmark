/-
Problem 70: Collinear Points and Mutually Visible Points

Fix integers k, ℓ. Is it true that, given a set of n ≥ n₀(k, ℓ) points in ℝ²,
either some k of them lie on a line, or some ℓ of them are 'mutually visible',
that is to say that the line segment joining any two of them contains no other
point from the set?

This question was first raised in the literature. It is known for ℓ ≤ 5.
-/

import Mathlib

open Set

namespace Green70

/-- A set of points in ℝ² is collinear if they all lie on a single line.
    We use the affine notion: points are collinear if they lie in a 1-dimensional
    affine subspace (or less). -/
def IsCollinear (S : Set (EuclideanSpace ℝ (Fin 2))) : Prop :=
  Collinear ℝ S

/-- The open segment between two points (excluding endpoints) -/
def openSegment' (p q : EuclideanSpace ℝ (Fin 2)) : Set (EuclideanSpace ℝ (Fin 2)) :=
  openSegment ℝ p q

/-- Two points p, q in a set A are mutually visible (with respect to A) if
    the open line segment between them contains no point from A. -/
def AreMutuallyVisible (A : Set (EuclideanSpace ℝ (Fin 2)))
    (p q : EuclideanSpace ℝ (Fin 2)) : Prop :=
  Disjoint (openSegment' p q) A

/-- A subset S of A consists of mutually visible points if for every pair of
    distinct points in S, the open segment between them contains no other
    point from A. -/
def IsMutuallyVisibleSubset (A S : Set (EuclideanSpace ℝ (Fin 2))) : Prop :=
  S ⊆ A ∧ ∀ p ∈ S, ∀ q ∈ S, p ≠ q → AreMutuallyVisible A p q

/-- A finite set A has k collinear points if there exists a subset of size k
    that is collinear. -/
def HasKCollinearPoints (A : Finset (EuclideanSpace ℝ (Fin 2))) (k : ℕ) : Prop :=
  ∃ S : Finset (EuclideanSpace ℝ (Fin 2)), S ⊆ A ∧ S.card = k ∧ IsCollinear ↑S

/-- A finite set A has ℓ mutually visible points if there exists a subset of
    size ℓ where every pair is mutually visible. -/
def HasLMutuallyVisiblePoints (A : Finset (EuclideanSpace ℝ (Fin 2))) (l : ℕ) : Prop :=
  ∃ S : Finset (EuclideanSpace ℝ (Fin 2)), S ⊆ A ∧ S.card = l ∧ IsMutuallyVisibleSubset ↑A ↑S

/-- Problem 70 Conjecture: For any k ≥ 2 and ℓ ≥ 2, there exists n₀ such that
    any finite set of at least n₀ points in ℝ² either contains k collinear
    points or ℓ mutually visible points. -/
def problem70Conjecture : Prop :=
  ∀ k l : ℕ, 2 ≤ k → 2 ≤ l →
    ∃ n₀ : ℕ, ∀ (A : Finset (EuclideanSpace ℝ (Fin 2))),
      n₀ ≤ A.card → HasKCollinearPoints A k ∨ HasLMutuallyVisiblePoints A l

/-- The main theorem statement (open problem). -/
theorem green_problem_70 : problem70Conjecture := by
  sorry

/-- Known case: The conjecture holds for ℓ ≤ 5. -/
theorem problem70_known_for_l_le_5 (k l : ℕ) (hk : 2 ≤ k) (hl : 2 ≤ l) (hl5 : l ≤ 5) :
    ∃ n₀ : ℕ, ∀ (A : Finset (EuclideanSpace ℝ (Fin 2))),
      n₀ ≤ A.card → HasKCollinearPoints A k ∨ HasLMutuallyVisiblePoints A l := by
  sorry

end Green70
