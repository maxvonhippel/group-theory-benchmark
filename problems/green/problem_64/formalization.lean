/-
Problem 64. Do there exist infinitely many primes for which p − 2 has an odd number of prime factors?

Comments. The same question may be asked with p − 1 (and this is probably more natural) but
with p − 2 the question is a weak form of the twin prime conjecture. The set of integers S
with an odd number of prime factors has density 1/2, so one is 'only' asking for infinitely
many primes in a set (S + 1) of density 1/2.

We formalize:
1. The definition of the set of primes p where Ω(p-2) is odd
2. The main conjecture: this set is infinite
3. Related variants (p-1 instead of p-2)
-/

import Mathlib

open ArithmeticFunction

namespace Green64

/-- Ω(n) is the number of prime factors of n counted with multiplicity.
    We use `cardFactors` from Mathlib. -/
abbrev Omega (n : ℕ) : ℕ := cardFactors n

/-- The set of primes p such that p - 2 has an odd number of prime factors
    (counted with multiplicity). -/
def primesWithOddOmegaMinusTwo : Set ℕ :=
  { p | Nat.Prime p ∧ Odd (Omega (p - 2)) }

/-- The set of primes p such that p - 1 has an odd number of prime factors
    (the more natural variant mentioned in the comments). -/
def primesWithOddOmegaMinusOne : Set ℕ :=
  { p | Nat.Prime p ∧ Odd (Omega (p - 1)) }

/-- Problem 64: There exist infinitely many primes p for which p - 2 has an
    odd number of prime factors (counted with multiplicity). -/
theorem green_problem_64 : primesWithOddOmegaMinusTwo.Infinite := by
  sorry

/-- The variant for p - 1: there exist infinitely many primes p for which
    p - 1 has an odd number of prime factors. -/
theorem green_problem_64_variant : primesWithOddOmegaMinusOne.Infinite := by
  sorry

/-- The set of natural numbers with an odd number of prime factors has
    natural density 1/2. This is related to the Liouville function λ(n) = (-1)^Ω(n). -/
theorem odd_omega_density_half :
    Filter.Tendsto (fun N => ({n ∈ Finset.range N | Odd (Omega n)}.card : ℚ) / N)
      Filter.atTop (nhds (1/2 : ℚ)) := by
  sorry

end Green64
