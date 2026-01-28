/-
Kourovka Notebook Problem 4.65 (J. G. Thompson)

Conjecture: (p^q − 1)/(p − 1) never divides (q^p − 1)/(q − 1)
if p, q are distinct primes.

The validity of this conjecture would simplify the proof of solvability
of groups of odd order (W. Feit, J. G. Thompson, Pacific J. Math., 13,
no. 3 (1963), 775–1029), rendering unnecessary the detailed use of
generators and relations.
-/

import Mathlib

open Nat

/-- For p > 1 and positive q, (p^q - 1)/(p - 1) is well-defined
    and equals 1 + p + p^2 + ... + p^(q-1) -/
def repunit (p q : ℕ) : ℕ := (p ^ q - 1) / (p - 1)

/-- Thompson's conjecture: For distinct primes p and q,
    (p^q - 1)/(p - 1) does not divide (q^p - 1)/(q - 1) -/
theorem thompson_conjecture :
    ∀ p q : ℕ, Nat.Prime p → Nat.Prime q → p ≠ q →
    ¬ (repunit p q ∣ repunit q p) := by
  sorry
