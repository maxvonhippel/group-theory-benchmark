/-
Problem 46 (Jacobsthal Problem):
What is the largest y for which one may cover the interval [y] by residue classes
a_p (mod p), one for each prime p ≤ x?

This is the Jacobsthal problem. It is known that:
- Lower bound: y ≫ x * log(x) * log(log(log(x))) / log(log(x))
- Upper bound: y ≪ x² (due to Iwaniec)
- Conjectured: y ≪ x^(1+o(1))

We formalize:
1. The definition of covering by residue classes
2. The Jacobsthal function g(x)
3. Known bounds as theorems with sorry
-/

import Mathlib

namespace Green46

open Nat Finset

/-- The set of primes up to and including x -/
def primesUpTo (x : ℕ) : Finset ℕ :=
  (Finset.range (x + 1)).filter Nat.Prime

/-- A covering assignment: for each prime p ≤ x, we choose a residue class a_p ∈ {0, ..., p-1} -/
def ResidueAssignment (x : ℕ) := (p : ℕ) → p ∈ primesUpTo x → ℕ

/-- An integer n is covered by the assignment if n ≡ a_p (mod p) for some prime p ≤ x -/
def isCovered (x : ℕ) (assignment : ResidueAssignment x) (n : ℕ) : Prop :=
  ∃ (p : ℕ) (hp : p ∈ primesUpTo x), n % p = (assignment p hp) % p

/-- The interval {1, 2, ..., y} is fully covered by the assignment -/
def intervalCovered (x y : ℕ) (assignment : ResidueAssignment x) : Prop :=
  ∀ n : ℕ, 1 ≤ n → n ≤ y → isCovered x assignment n

/-- There exists an assignment that covers the interval {1, ..., y} -/
def canCoverInterval (x y : ℕ) : Prop :=
  ∃ assignment : ResidueAssignment x, intervalCovered x y assignment

/-- The Jacobsthal function g(x): the largest y such that [1, y] can be covered
    by residue classes a_p (mod p), one for each prime p ≤ x.

    We define it as the supremum of all y that can be covered. -/
noncomputable def jacobsthal (x : ℕ) : ℕ :=
  sSup {y : ℕ | canCoverInterval x y}

/-- Basic property: if y can be covered, so can any smaller interval -/
theorem canCover_mono {x y₁ y₂ : ℕ} (h : y₁ ≤ y₂) (hcover : canCoverInterval x y₂) :
    canCoverInterval x y₁ := by
  obtain ⟨assignment, hcov⟩ := hcover
  exact ⟨assignment, fun n hn1 hn2 => hcov n hn1 (le_trans hn2 h)⟩

/-- The empty interval is always coverable -/
theorem canCover_zero (x : ℕ) : canCoverInterval x 0 := by
  use fun _ _ => 0
  intro n hn1 hn2
  omega

/-- For any x ≥ 2, we can cover at least the interval [1, 1] since 2 is prime -/
theorem canCover_one (x : ℕ) (hx : x ≥ 2) : canCoverInterval x 1 := by
  sorry

/-- The Jacobsthal function is monotone in x -/
theorem jacobsthal_mono {x₁ x₂ : ℕ} (h : x₁ ≤ x₂) : jacobsthal x₁ ≤ jacobsthal x₂ := by
  sorry

/-- Main theorem: The Jacobsthal function satisfies known lower bounds.
    It is known that g(x) ≫ x * log(x) * log(log(log(x))) / log(log(x)) -/
theorem jacobsthal_lower_bound :
    ∃ c : ℝ, c > 0 ∧ ∀ x : ℕ, x ≥ 16 →
      (jacobsthal x : ℝ) ≥ c * x * Real.log x * Real.log (Real.log (Real.log x)) /
        Real.log (Real.log x) := by
  sorry

/-- Main theorem: The Jacobsthal function satisfies the upper bound g(x) ≪ x² (Iwaniec) -/
theorem jacobsthal_upper_bound :
    ∃ C : ℝ, C > 0 ∧ ∀ x : ℕ, x ≥ 2 →
      (jacobsthal x : ℝ) ≤ C * (x : ℝ)^2 := by
  sorry

/-- Conjectured: g(x) ≪ x^(1+o(1)), meaning for any ε > 0, eventually g(x) ≤ x^(1+ε) -/
theorem jacobsthal_conjectured_bound :
    ∀ ε : ℝ, ε > 0 → ∃ N : ℕ, ∀ x : ℕ, x ≥ N →
      (jacobsthal x : ℝ) ≤ (x : ℝ)^(1 + ε) := by
  sorry

/-- The Jacobsthal function is finite for all x (upper bounded by x²) -/
theorem jacobsthal_finite (x : ℕ) (hx : x ≥ 2) : jacobsthal x < x^2 + 1 := by
  sorry

end Green46
