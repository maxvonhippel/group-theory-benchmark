import Mathlib

/-!
# Problem 65

Is there c > 0 with the following property: whenever A ⊂ [N] is a set of size N^(1−c),
A − A contains a nonzero square? What about A − A containing a prime minus one?

Here [N] denotes the set {1, 2, ..., N}, and A - A = {a - b : a, b ∈ A} is the difference set.
-/

/-- The interval [N] = {1, 2, ..., N} as a finset -/
def intervalN (N : ℕ) : Finset ℕ := Finset.Icc 1 N

/-- The difference set A - A for integer subsets, viewed as a set of integers -/
def diffSet (A : Finset ℕ) : Set ℤ :=
  {d : ℤ | ∃ a b : ℕ, a ∈ A ∧ b ∈ A ∧ d = (a : ℤ) - (b : ℤ)}

/-- A positive integer is a nonzero perfect square -/
def isNonzeroSquare (d : ℤ) : Prop :=
  d ≠ 0 ∧ ∃ k : ℤ, k ≠ 0 ∧ d = k * k

/-- A positive integer is of the form (prime - 1) -/
def isPrimeMinusOne (d : ℤ) : Prop :=
  ∃ p : ℕ, Nat.Prime p ∧ d = (p : ℤ) - 1

/-- Problem 65a: Does there exist c > 0 such that for all sufficiently large N,
    if A ⊆ [N] has size at least N^(1-c), then A - A contains a nonzero square? -/
def problem65a : Prop :=
  ∃ c : ℝ, c > 0 ∧
    ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
      ∀ A : Finset ℕ, A ⊆ intervalN N →
        (A.card : ℝ) ≥ (N : ℝ) ^ (1 - c) →
          ∃ d ∈ diffSet A, isNonzeroSquare d

/-- Problem 65b: Does there exist c > 0 such that for all sufficiently large N,
    if A ⊆ [N] has size at least N^(1-c), then A - A contains a prime minus one? -/
def problem65b : Prop :=
  ∃ c : ℝ, c > 0 ∧
    ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
      ∀ A : Finset ℕ, A ⊆ intervalN N →
        (A.card : ℝ) ≥ (N : ℝ) ^ (1 - c) →
          ∃ d ∈ diffSet A, isPrimeMinusOne d

/-- The full problem 65 asks about both statements -/
theorem problem65 : problem65a ∧ problem65b := by
  sorry
