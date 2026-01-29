import Mathlib

/-!
# Green's Problem 44 - Sieving by Residue Classes

**Problem Statement:**
Sieve [N] by removing half the residue classes mod pᵢ, for primes
2 ≤ p₁ < p₂ < ··· < p₁₀₀₀ < N^{9/10}. Does the remaining set have size at most (1/10)N?

**Interpretation:**
Given N, we choose 1000 distinct primes p₁ < p₂ < ... < p₁₀₀₀, all less than N^{9/10},
with p₁ ≥ 2. For each prime pᵢ, we remove at least ⌊pᵢ/2⌋ residue classes from [N].
The question asks whether the remaining set always has cardinality at most N/10.

**Comments:** Erdős remarks that the answer is affirmative if the primes are all less
than N^{1/2}, by the large sieve.
-/

open Nat Finset

noncomputable section

/-- A selection of residue classes to remove for a given prime p.
    We require removing at least ⌊p/2⌋ residue classes. -/
structure SieveChoice (p : ℕ) where
  /-- The set of residue classes to remove (elements are in {0, 1, ..., p-1}) -/
  removed : Finset (Fin p)
  /-- We must remove at least half of the residue classes -/
  half_removed : removed.card ≥ p / 2

/-- A sequence of 1000 distinct primes satisfying the constraints for problem 44 -/
structure PrimeSequence (N : ℕ) where
  /-- The sequence of 1000 primes (as a function from Fin 1000) -/
  primes : Fin 1000 → ℕ
  /-- Each entry is prime -/
  all_prime : ∀ i, (primes i).Prime
  /-- The primes are strictly increasing -/
  strictly_increasing : StrictMono primes
  /-- All primes are at least 2 (follows from primality) -/
  ge_two : ∀ i, primes i ≥ 2
  /-- All primes are less than N^{9/10} -/
  upper_bound : ∀ i, (primes i : ℝ) < (N : ℝ) ^ (9 / 10 : ℝ)

/-- An element n survives the sieve for prime p with choice c if n's residue class is not removed -/
def survivesPrime (p : ℕ) (hp : p ≥ 2) (c : SieveChoice p) (n : ℕ) : Bool :=
  (⟨n % p, Nat.mod_lt n (by omega)⟩ : Fin p) ∉ c.removed

/-- An element survives all primes in the sieve -/
def survivesAll (N : ℕ) (ps : PrimeSequence N)
    (choices : ∀ i : Fin 1000, SieveChoice (ps.primes i)) (n : ℕ) : Bool :=
  decide (∀ i : Fin 1000, survivesPrime (ps.primes i) (ps.ge_two i) (choices i) n = true)

/-- The surviving set after sieving [N] = {1, ..., N} using the given primes and choices -/
def survivingSet (N : ℕ) (ps : PrimeSequence N)
    (choices : ∀ i : Fin 1000, SieveChoice (ps.primes i)) : Finset ℕ :=
  (Finset.Icc 1 N).filter fun n => survivesAll N ps choices n

/--
**Green's Problem 44:**

For all N and for all valid choices of 1000 primes p₁ < p₂ < ... < p₁₀₀₀ < N^{9/10}
(with p₁ ≥ 2), and for all choices of which half of the residue classes to remove
for each prime, is the remaining subset of [N] always of size at most N/10?

Note: The bound N/10 is exact, but due to integer division we state it as ≤ N / 10.
-/
theorem green_problem_44 :
    ∀ (N : ℕ) (hN : N > 0) (ps : PrimeSequence N)
      (choices : ∀ i : Fin 1000, SieveChoice (ps.primes i)),
    (survivingSet N ps choices).card ≤ N / 10 := by
  sorry

/--
**Known result (Erdős via Large Sieve):**

If we use primes less than N^{1/2} instead of N^{9/10}, then the bound holds.
-/
structure PrimeSequenceSmall (N : ℕ) extends PrimeSequence N where
  /-- Stronger bound: all primes are less than N^{1/2} -/
  small_bound : ∀ i, (primes i : ℝ) < (N : ℝ) ^ (1 / 2 : ℝ)

theorem erdos_result_small_primes :
    ∀ (N : ℕ) (hN : N > 0) (ps : PrimeSequenceSmall N)
      (choices : ∀ i : Fin 1000, SieveChoice (ps.primes i)),
    (survivingSet N ps.toPrimeSequence choices).card ≤ N / 10 := by
  sorry

end
