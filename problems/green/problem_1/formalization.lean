import Mathlib

/-!
# Green's Problem 1: Sum-free sets

Let A be a set of n positive integers. Does A contain a sum-free subset
of size at least n/3 + Ω(n), where Ω(n) → ∞ as n → ∞?

This is a well-known open problem. Bourgain showed that every set of n positive
integers contains a sum-free subset of size at least (n+2)/3, so the question is
whether this bound can be improved by an unbounded additive term.
-/

/-- A set S is sum-free if for all a, b ∈ S, we have a + b ∉ S. -/
def IsSumFree (S : Finset ℕ) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, a + b ∉ S

/-- The main problem: Does there exist a function f : ℕ → ℝ that tends to infinity,
such that every finite set A of positive integers contains a sum-free
subset of size at least |A|/3 + f(|A|)?

This captures the question "can we beat n/3 by an unbounded amount?" -/
def GreenProblem1 : Prop :=
  ∃ f : ℕ → ℝ,
    Filter.Tendsto f Filter.atTop Filter.atTop ∧
    ∀ (A : Finset ℕ), (∀ a ∈ A, 0 < a) →
      ∃ S : Finset ℕ, S ⊆ A ∧ IsSumFree S ∧
        (S.card : ℝ) ≥ (A.card : ℝ) / 3 + f A.card

/-- Bourgain's known result: every set of n positive integers contains a
sum-free subset of size at least (n+2)/3. -/
theorem bourgain_sum_free_lower_bound (A : Finset ℕ) (hA : ∀ a ∈ A, 0 < a) :
    ∃ S : Finset ℕ, S ⊆ A ∧ IsSumFree S ∧ 3 * S.card ≥ A.card + 2 := by
  sorry

/-- The problem is open: we don't know if GreenProblem1 is true or false. -/
theorem green_problem_1_open : GreenProblem1 ∨ ¬GreenProblem1 := by
  sorry
