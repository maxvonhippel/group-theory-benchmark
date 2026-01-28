import Mathlib

/-!
# Green's Problem 46: The Jacobsthal Problem

What is the largest y for which one may cover the interval [y] by residue classes
a_p (mod p), one for each prime p ≤ x?

This formalizes the Jacobsthal function g(x), defined as the largest y such that
the interval {1, 2, ..., y} can be covered by choosing one residue class a_p (mod p)
for each prime p ≤ x.

Known bounds:
- Lower bound (Rankin): g(x) ≫ x log x log log log x / log log x
- Upper bound (Iwaniec): g(x) ≪ x²
- Conjectured: g(x) ≪ x^(1+o(1))
-/

open Nat Finset

namespace Green46

/-- The set of primes up to and including x -/
def primesUpTo (x : ℕ) : Finset ℕ :=
  (Finset.range (x + 1)).filter Nat.Prime

/-- A covering assignment: for each prime p ≤ x, we choose a residue class representative -/
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

/-- The Jacobsthal function g(x): the supremum of all y that can be covered
    by residue classes a_p (mod p), one for each prime p ≤ x -/
noncomputable def jacobsthal (x : ℕ) : ℕ :=
  sSup {y : ℕ | canCoverInterval x y}

/-- The set of coverable intervals is bounded (Iwaniec's result implies this) -/
theorem canCoverInterval_bounded (x : ℕ) : BddAbove {y : ℕ | canCoverInterval x y} := by
  sorry

/-- Main theorem: The Jacobsthal function satisfies known lower bounds.
    It is known that g(x) ≫ x * log(x) * log(log(log(x))) / log(log(x)) -/
theorem jacobsthal_lower_bound :
    ∃ c : ℝ, c > 0 ∧ ∀ x : ℕ, x ≥ 3 →
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

/-- Basic property: if y can be covered, so can any smaller interval -/
theorem canCover_mono {x y₁ y₂ : ℕ} (h : y₁ ≤ y₂) (hcover : canCoverInterval x y₂) :
    canCoverInterval x y₁ := by
  obtain ⟨assignment, hcov⟩ := hcover
  exact ⟨assignment, fun n hn1 hn2 => hcov n hn1 (le_trans hn2 h)⟩

/-- The empty interval is trivially covered -/
theorem canCover_zero (x : ℕ) : canCoverInterval x 0 := by
  use fun _ _ => 0
  intro n hn1 hn0
  omega

/-- For any x ≥ 2, we can at least cover some positive interval -/
theorem canCover_positive (x : ℕ) (hx : x ≥ 2) : canCoverInterval x 1 := by
  sorry

/-- g(x) is the largest coverable interval -/
theorem jacobsthal_is_max (x : ℕ) (y : ℕ) (hy : canCoverInterval x y) :
    y ≤ jacobsthal x := by
  exact le_csSup (canCoverInterval_bounded x) hy

/-- If y > g(x), then [1, y] cannot be covered -/
theorem jacobsthal_optimal (x : ℕ) (y : ℕ) (hy : y > jacobsthal x) :
    ¬ canCoverInterval x y := by
  intro hcover
  have := jacobsthal_is_max x y hcover
  omega

end Green46
