import Mathlib

/-!
# Problem 62: Products of Two Primes Modulo a Prime

Let p be a large prime, and let A be the set of all primes less than p.
Is every x ∈ {1, ..., p − 1} congruent to some product a₁a₂ where a₁, a₂ ∈ A?

This is a problem of Erdős, Odlyzko and Sárközy from 1987.
-/

open Nat

/-- The set of all primes less than p -/
def primesLessThan (p : ℕ) : Set ℕ := {q : ℕ | q.Prime ∧ q < p}

/-- The conjecture: For sufficiently large primes p, every nonzero element mod p
    is congruent to a product of two primes less than p -/
theorem erdos_odlyzko_sarkozy_conjecture :
    ∃ N : ℕ, ∀ p : ℕ, p.Prime → p > N →
      ∀ x : ZMod p, x ≠ 0 →
        ∃ a₁ a₂ : ℕ, a₁ ∈ primesLessThan p ∧ a₂ ∈ primesLessThan p ∧
          (a₁ * a₂ : ZMod p) = x := by
  sorry

/-- A stronger version asking if this holds for all primes p (not just sufficiently large) -/
theorem erdos_odlyzko_sarkozy_conjecture_all_primes :
    ∀ p : ℕ, p.Prime → p > 2 →
      ∀ x : ZMod p, x ≠ 0 →
        ∃ a₁ a₂ : ℕ, a₁ ∈ primesLessThan p ∧ a₂ ∈ primesLessThan p ∧
          (a₁ * a₂ : ZMod p) = x := by
  sorry

/-- Walker's result: Every nonzero element mod p is a product of at most 6 primes less than p
    (for sufficiently large p) -/
theorem walker_six_primes :
    ∃ N : ℕ, ∀ p : ℕ, p.Prime → p > N →
      ∀ x : ZMod p, x ≠ 0 →
        ∃ primes : List ℕ, primes.length ≤ 6 ∧
          (∀ q ∈ primes, q ∈ primesLessThan p) ∧
          (primes.prod : ZMod p) = x := by
  sorry

/-- Shparlinski's improvement: 5 primes suffice -/
theorem shparlinski_five_primes :
    ∃ N : ℕ, ∀ p : ℕ, p.Prime → p > N →
      ∀ x : ZMod p, x ≠ 0 →
        ∃ primes : List ℕ, primes.length ≤ 5 ∧
          (∀ q ∈ primes, q ∈ primesLessThan p) ∧
          (primes.prod : ZMod p) = x := by
  sorry

/-- Matomäki-Teräväinen 2023: 3 primes suffice -/
theorem matomaki_teravainen_three_primes :
    ∃ N : ℕ, ∀ p : ℕ, p.Prime → p > N →
      ∀ x : ZMod p, x ≠ 0 →
        ∃ a₁ a₂ a₃ : ℕ, a₁ ∈ primesLessThan p ∧ a₂ ∈ primesLessThan p ∧ a₃ ∈ primesLessThan p ∧
          (a₁ * a₂ * a₃ : ZMod p) = x := by
  sorry
