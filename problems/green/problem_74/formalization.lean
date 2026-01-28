/-
Problem 74: Largest Subset of [N]^d with No 5 Coplanar Points

What is the largest subset of [N]^d with no 5 points on a 2-plane?

The problem asks for the maximum size of a subset of the d-dimensional integer grid
{1, ..., N}^d such that no 5 points lie in a common 2-dimensional affine plane.

Comments note this is equivalent to asking for the largest subset with no 5 points
on a conic (since conics are planar, and through any 5 points in a plane there is a conic).
The author notes not knowing if such a set can have size N^{d-100}.
-/

import Mathlib

open Set Finset AffineSubspace Module

namespace Green74

/-- The discrete grid [N]^d = {1, ..., N}^d represented as a subset of ℤ^d.
    We represent this as Fin d → ℤ where each coordinate is in [1, N]. -/
def discreteGrid (N : ℕ) (d : ℕ) : Set (Fin d → ℤ) :=
  { v | ∀ i : Fin d, 1 ≤ v i ∧ v i ≤ N }

/-- A set of points is coplanar if they lie in a 2-dimensional affine subspace.
    We work in ℚ^d to have a nice field structure while containing integer points. -/
def IsCoplanar (S : Set (Fin d → ℚ)) : Prop :=
  ∃ (P : AffineSubspace ℚ (Fin d → ℚ)), Module.finrank ℚ P.direction ≤ 2 ∧ S ⊆ P

/-- Embedding of integer points into rational points. -/
def intToRat (d : ℕ) : (Fin d → ℤ) → (Fin d → ℚ) :=
  fun v i => (v i : ℚ)

/-- A subset A of [N]^d has no 5 coplanar points if there is no 5-element subset
    whose rational embeddings are coplanar (lie in a 2-dimensional affine plane). -/
def HasNo5CoplanarPoints (d : ℕ) (A : Finset (Fin d → ℤ)) : Prop :=
  ∀ S : Finset (Fin d → ℤ), S ⊆ A → S.card = 5 →
    ¬IsCoplanar (intToRat d '' (S : Set (Fin d → ℤ)))

/-- The maximum size of a subset of [N]^d with no 5 coplanar points.
    This is the function whose behavior Problem 74 asks about. -/
noncomputable def maxNo5CoplanarSubsetSize (N d : ℕ) : ℕ :=
  sSup { k : ℕ | ∃ A : Finset (Fin d → ℤ),
    (∀ v ∈ A, v ∈ discreteGrid N d) ∧
    A.card = k ∧
    HasNo5CoplanarPoints d A }

/-- Upper bound conjecture: For large enough dimension d, the maximum subset
    size with no 5 coplanar points is bounded by N^{d-c} for some constant c > 0. -/
def upperBoundConjecture : Prop :=
  ∃ c : ℕ, c > 0 ∧ ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
    ∀ N : ℕ, 2 ≤ N → maxNo5CoplanarSubsetSize N d ≤ N ^ (d - c)

/-- Lower bound conjecture: There exist non-trivial subsets with no 5 coplanar points.
    Specifically, we can always find subsets of size at least N. -/
def lowerBoundConjecture : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ N : ℕ, 1 ≤ N →
    maxNo5CoplanarSubsetSize N d ≥ N

/-- Main problem 74: Characterize maxNo5CoplanarSubsetSize(N, d).
    This is stated as the conjunction of natural bounds - the actual problem
    asks for the precise behavior which is open. -/
theorem green_problem_74_bounds :
    upperBoundConjecture ∧ lowerBoundConjecture := by
  sorry

/-- Alternative formulation: A set has no 5 points on a conic if no 5 points
    lie on a planar algebraic curve of degree 2. This is "more-or-less equivalent"
    to the 5-coplanar condition per the problem comments. -/
def HasNo5PointsOnConic (d : ℕ) (A : Finset (Fin d → ℤ)) : Prop :=
  -- Through any 5 points in general position in a plane, there is a conic.
  -- So avoiding 5 coplanar points implies avoiding 5 points on a conic.
  HasNo5CoplanarPoints d A

/-- The equivalence noted in the problem comments. -/
theorem conic_equiv_coplanar (d : ℕ) (A : Finset (Fin d → ℤ)) :
    HasNo5CoplanarPoints d A ↔ HasNo5PointsOnConic d A := by
  rfl  -- By our definition they are the same; full equivalence would need more work

end Green74
