/-
Problem 60. Is there an absolute constant c > 0 such that, if A ⊂ ℕ is a set of squares
of size at least 2, then |A + A| ≥ |A|^{1+c}?

This formalizes the question: does there exist c > 0 such that for every finite set A
of perfect squares with |A| ≥ 2, the sumset A + A has cardinality at least |A|^{1+c}.
-/

import Mathlib

open Finset Real

/-- A natural number is a perfect square -/
def IsPerfectSquare (n : ℕ) : Prop := ∃ k : ℕ, n = k ^ 2

/-- A finite set of natural numbers consists entirely of perfect squares -/
def IsSetOfSquares (A : Finset ℕ) : Prop := ∀ a ∈ A, IsPerfectSquare a

/-- The sumset A + A of a finite set A ⊂ ℕ -/
def sumset (A : Finset ℕ) : Finset ℕ := (A ×ˢ A).image (fun p => p.1 + p.2)

/--
Problem 60: Is there an absolute constant c > 0 such that, if A ⊂ ℕ is a set of squares
of size at least 2, then |A + A| ≥ |A|^{1+c}?

This states the existence of such a constant c.
-/
theorem green_problem_60 :
    ∃ c : ℝ, c > 0 ∧
      ∀ A : Finset ℕ, IsSetOfSquares A → A.card ≥ 2 →
        (A.card : ℝ) ^ (1 + c) ≤ ((sumset A).card : ℝ) := by
  sorry
