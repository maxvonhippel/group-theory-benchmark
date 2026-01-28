/-
Problem 54. Let K ⊂ R^N be a balanced compact set (that is, λK ⊂ K when |λ| ⩽ 1)
and suppose that the normalised Gaussian measure γ∞(K) is at least 0.99.
Does 10K (say) contain a compact convex set C with γ∞(C) ⩾ 0.01?
-/

import Mathlib

open MeasureTheory Set Topology

/-
The standard Gaussian measure on ℝ^ℕ (infinite product of standard Gaussian measures).
We define it as the infinite product measure of the standard Gaussian on each coordinate.
-/
noncomputable def stdGaussianOnR : Measure ℝ :=
  ProbabilityTheory.gaussianReal 0 1

/-
The standard Gaussian measure on ℝ^ℕ as an infinite product.
-/
noncomputable def stdGaussianInf : Measure (ℕ → ℝ) :=
  Measure.infinitePi (fun _ => stdGaussianOnR)

/-
Scalar multiplication of a set by a real number.
-/
def scalarMult (r : ℝ) (K : Set (ℕ → ℝ)) : Set (ℕ → ℝ) :=
  { x | ∃ y ∈ K, x = r • y }

/-
Problem 54: Let K ⊂ ℝ^ℕ be a balanced compact set with γ∞(K) ≥ 0.99.
Does 10K contain a compact convex set C with γ∞(C) ≥ 0.01?

This is formalized as asking whether such a set C always exists.
-/
theorem green_problem_54 :
  ∀ (K : Set (ℕ → ℝ)),
    IsCompact K →
    Balanced ℝ K →
    stdGaussianInf K ≥ 0.99 →
    ∃ (C : Set (ℕ → ℝ)),
      C ⊆ scalarMult 10 K ∧
      IsCompact C ∧
      Convex ℝ C ∧
      stdGaussianInf C ≥ 0.01 := by
  sorry
