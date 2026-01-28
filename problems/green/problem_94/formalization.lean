/-
Problem 94. Let A ⊂ ℝ be a set of positive measure. Does A contain an affine copy of {1, 1/2, 1/4, ...}?
Comments: This is a special case of the Erdős similarity problem.

Formalization: We ask whether for every measurable set A ⊆ ℝ with positive Lebesgue measure,
there exist a, b ∈ ℝ with a ≠ 0 such that for all n ∈ ℕ, a * (1/2)^n + b ∈ A.
-/

import Mathlib

open MeasureTheory Set

namespace Green94

/-- The geometric sequence {1, 1/2, 1/4, 1/8, ...} = {(1/2)^n : n ∈ ℕ} -/
def geometricSeq : Set ℝ := {x : ℝ | ∃ n : ℕ, x = (1/2 : ℝ)^n}

/-- An affine copy of a set S is a set {a * s + b : s ∈ S} for some a ≠ 0 and b ∈ ℝ -/
def affineImage (a b : ℝ) (S : Set ℝ) : Set ℝ := {y : ℝ | ∃ s ∈ S, y = a * s + b}

/-- A set A contains an affine copy of S if there exist a ≠ 0 and b such that
    the affine image of S is contained in A -/
def containsAffineCopy (A S : Set ℝ) : Prop :=
  ∃ a b : ℝ, a ≠ 0 ∧ affineImage a b S ⊆ A

/-- The Erdős Similarity Conjecture (special case for geometric sequence):
    Every set of positive Lebesgue measure contains an affine copy of {1, 1/2, 1/4, ...} -/
theorem erdos_similarity_geometric :
    ∀ A : Set ℝ, MeasurableSet A → 0 < volume A →
    containsAffineCopy A geometricSeq := by
  sorry

end Green94
