/-
Problem 16. What is the largest subset of [N] with no solution to x+3y = 2z+2w in distinct integers x, y, z, w?

Comments. This question was asked by Ruzsa [239, Section 9]. Writing f(N) for the number in question,
so far as I know the best bounds known are N^{1/2} ≪ f(N) ≪ Ne^{-c(log N)^{1/7}},
the lower bound being in Ruzsa's paper and the upper bound being due to Schoen and Sisask [253].

We formalize:
1. The definition of a set avoiding the equation x + 3y = 2z + 2w in distinct elements
2. The function f(N) = maximum size of such a subset of [N]
3. The known asymptotic bounds
-/

import Mathlib

open scoped BigOperators

namespace Green16

/-- The interval [N] = {1, 2, ..., N} -/
def interval (N : ℕ) : Finset ℕ := Finset.Icc 1 N

/-- A set S avoids the equation x + 3y = 2z + 2w in distinct elements if
    there do not exist pairwise distinct x, y, z, w ∈ S with x + 3y = 2z + 2w -/
def AvoidsEquation {α : Type*} [Add α] [Mul α] [OfNat α 2] [OfNat α 3] (S : Set α) : Prop :=
  ∀ x y z w, x ∈ S → y ∈ S → z ∈ S → w ∈ S →
    x ≠ y → x ≠ z → x ≠ w → y ≠ z → y ≠ w → z ≠ w →
    x + 3 * y ≠ 2 * z + 2 * w

/-- The maximum size of a subset of [N] that avoids x + 3y = 2z + 2w -/
noncomputable def f (N : ℕ) : ℕ :=
  sSup {k | ∃ S : Finset ℕ, S ⊆ interval N ∧ AvoidsEquation (S : Set ℕ) ∧ S.card = k}

/-- f(N) is well-defined and bounded by N -/
theorem f_le (N : ℕ) : f N ≤ N := by
  sorry

/-- The trivial lower bound: f(N) ≥ 1 for N ≥ 1 -/
theorem f_ge_one (N : ℕ) (hN : N ≥ 1) : f N ≥ 1 := by
  sorry

/-- Ruzsa's lower bound: f(N) ≥ c * √N for some constant c > 0 -/
theorem ruzsa_lower_bound :
    ∃ c : ℝ, c > 0 ∧ ∀ᶠ N in Filter.atTop, (f N : ℝ) ≥ c * Real.sqrt N := by
  sorry

/-- Schoen-Sisask upper bound: f(N) ≤ N * e^{-c(log N)^{1/7}} for some constant c > 0
    and all sufficiently large N -/
theorem schoen_sisask_upper_bound :
    ∃ c : ℝ, c > 0 ∧ ∀ᶠ N in Filter.atTop,
      (f N : ℝ) ≤ N * Real.exp (-c * (Real.log N) ^ (1/7 : ℝ)) := by
  sorry

/-- The main open problem: determine the exact asymptotic behavior of f(N).
    The gap between N^{1/2} and N * e^{-c(log N)^{1/7}} is significant. -/
theorem green_problem_16 :
    ∃ g : ℕ → ℝ, (∀ᶠ N in Filter.atTop, (f N : ℝ) ≤ g N) ∧
                  (∀ᶠ N in Filter.atTop, (f N : ℝ) ≥ Real.sqrt N) ∧
                  (∀ᶠ N in Filter.atTop, g N ≤ N) := by
  sorry

end Green16
