import Mathlib

/-!
# Green's Problem 43

Let N be a large integer. For each prime p with N^{0.51} ≤ p < 2N^{0.51}, pick some residue
a(p) ∈ ℤ/pℤ. Is it true that
  #{n ∈ [N] : n ≡ a(p) (mod p) for some p} ≫ N^{1−o(1)}?

The conjecture asserts that for any ε > 0, for all sufficiently large N, and for any choice
of residues a(p), the count of n in {1, ..., N} satisfying n ≡ a(p) (mod p) for some prime p
in the given range is at least N^{1-ε}.
-/

open Nat Finset

noncomputable section

/-- The set of primes in the range [N^{0.51}, 2N^{0.51}) -/
def primesInRange (N : ℕ) : Finset ℕ :=
  (Finset.range (2 * Nat.ceil ((N : ℝ) ^ (0.51 : ℝ)) + 1)).filter fun p =>
    p.Prime ∧ (N : ℝ) ^ (0.51 : ℝ) ≤ (p : ℝ) ∧ (p : ℝ) < 2 * (N : ℝ) ^ (0.51 : ℝ)

/-- A residue assignment: for each prime p in the range, we pick a residue class a(p) -/
def ResidueAssignment (N : ℕ) := (p : ℕ) → (hp : p ∈ primesInRange N) → Fin p

/-- The count of n ∈ {1, ..., N} such that n ≡ a(p) (mod p) for some prime p in the range -/
def coverCount (N : ℕ) (a : ResidueAssignment N) : ℕ :=
  (Finset.range N).filter (fun n =>
    ∃ p : ℕ, ∃ hp : p ∈ primesInRange N, n % p = (a p hp).val) |>.card

/--
**Green's Conjecture (Problem 43):**

For any ε > 0, for all sufficiently large N, and for any choice of residues a(p),
the number of n ∈ {1, ..., N} satisfying n ≡ a(p) (mod p) for some prime p
in [N^{0.51}, 2N^{0.51}) is at least N^{1-ε}.

This is a quantitative statement that the covered set has size N^{1-o(1)}.
-/
theorem green_problem_43 :
    ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (a : ResidueAssignment N),
      (coverCount N a : ℝ) ≥ (N : ℝ) ^ (1 - ε) := by
  sorry

end

