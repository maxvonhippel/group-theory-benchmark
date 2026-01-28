/-
Problem 45. Can we pick residue classes aₚ (mod p), one for each prime p ≤ N,
such that every integer ≤ N lies in at least 10 of them?

Comments: This is raised in [101, Section 6, Problem 6]. Erdős remarks that he does
not know how to answer it with 10 replaced by 2.

**Interpretation:**
Given N, we want to find a function that assigns to each prime p ≤ N a residue class
aₚ ∈ {0, 1, ..., p-1}. Then we ask: can we choose such a function so that every
integer n with 1 ≤ n ≤ N lies in at least 10 of these residue classes?

An integer n lies in the residue class aₚ (mod p) if and only if n ≡ aₚ (mod p).
-/

import Mathlib

open Finset BigOperators Nat

namespace Green45

/-- The set of primes ≤ N -/
def primesUpTo (N : ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).filter Nat.Prime

/-- A choice of residue classes: for each prime p ≤ N, we pick a residue class aₚ ∈ {0, ..., p-1} -/
structure ResidueChoice (N : ℕ) where
  /-- For each prime p ≤ N, the chosen residue class (in ℤ/pℤ) -/
  choice : (p : ℕ) → p.Prime → p ≤ N → Fin p

/-- The number of residue classes containing n, for a given choice -/
noncomputable def coverageCount (N : ℕ) (n : ℕ) (rc : ResidueChoice N) : ℕ :=
  (primesUpTo N).filter (fun p =>
    if h : p.Prime ∧ p ≤ N then
      (rc.choice p h.1 h.2 : ℕ) = n % p
    else False
  ) |>.card

/-- Every integer in {1, ..., N} is covered at least k times -/
def hasMinCoverage (N : ℕ) (k : ℕ) (rc : ResidueChoice N) : Prop :=
  ∀ n : ℕ, 1 ≤ n → n ≤ N → coverageCount N n rc ≥ k

/--
**Green's Problem 45:**

For all sufficiently large N, can we pick residue classes aₚ (mod p), one for each
prime p ≤ N, such that every integer in {1, ..., N} lies in at least 10 of them?

We formalize this as an existence question for each N.
-/
def problem45 (N : ℕ) : Prop :=
  ∃ rc : ResidueChoice N, hasMinCoverage N 10 rc

/--
The main conjecture: For all sufficiently large N, problem45 N holds.
-/
theorem green_problem_45 : ∃ N₀ : ℕ, ∀ N ≥ N₀, problem45 N := by
  sorry

/--
Variant: The problem with 10 replaced by 2.
Erdős remarks that he does not know how to answer this variant either.
-/
def problem45_variant2 (N : ℕ) : Prop :=
  ∃ rc : ResidueChoice N, hasMinCoverage N 2 rc

/-- The variant question: Does problem45_variant2 hold for all sufficiently large N? -/
theorem green_problem_45_variant : ∃ N₀ : ℕ, ∀ N ≥ N₀, problem45_variant2 N := by
  sorry

end Green45
