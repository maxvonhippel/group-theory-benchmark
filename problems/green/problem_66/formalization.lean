/-
Problem 66. Is there always a sum of two squares between X − 1/10 X^{1/4} and X?

This asks whether for all sufficiently large real X, there exist integers a, b
such that X - (1/10) * X^{1/4} ≤ a² + b² ≤ X.
-/

import Mathlib

/--
Green's Problem 66: For all sufficiently large X, there exists a sum of two squares
in the interval [X - (1/10) * X^{1/4}, X].
-/
theorem green_problem_66 :
    ∃ X₀ : ℝ, ∀ X : ℝ, X ≥ X₀ →
      ∃ a b : ℤ, X - (1/10) * X^(1/4 : ℝ) ≤ (a^2 + b^2 : ℝ) ∧ (a^2 + b^2 : ℝ) ≤ X := by
  sorry
