/-
Problem 36: Sumset configurations in abelian groups and matrix multiplication

Do the following exist, for arbitrarily large n? An abelian group H with |H| = n^{2+o(1)},
together with subsets A_1, ..., A_n, B_1, ..., B_n satisfying:
  - |A_i||B_i| ≥ n^{2-o(1)}
  - |A_i + B_i| = |A_i||B_i| (i.e., the sumset is "direct")
  - The sets A_i + B_i are pairwise disjoint from A_j + B_k for j ≠ k

If true, this would imply that the exponent of matrix multiplication is 2.

We formalize this problem using:
- A configuration structure capturing the required properties for a specific n
- Asymptotic conditions expressed via sequences indexed by ℕ
- The existence question as: for arbitrarily large n, such configurations exist
-/

import Mathlib

open Finset BigOperators

namespace Green36

variable {H : Type*} [AddCommGroup H]

/-- The sumset A + B of two sets in an additive group -/
def sumset (A B : Set H) : Set H := {h | ∃ a ∈ A, ∃ b ∈ B, h = a + b}

/-- The sumset of two finsets -/
def finsetSumset [DecidableEq H] (A B : Finset H) : Finset H :=
  Finset.image (fun p : H × H => p.1 + p.2) (A ×ˢ B)

/-- A sumset is "direct" if |A + B| = |A| * |B|, meaning all sums are distinct -/
def IsDirectSumset [DecidableEq H] (A B : Finset H) : Prop :=
  (finsetSumset A B).card = A.card * B.card

/-- A configuration witnessing Problem 36 for a specific n and group H -/
structure SumsetConfiguration (H : Type*) [AddCommGroup H] [DecidableEq H] [Fintype H] (n : ℕ) where
  /-- The n families of sets A_i -/
  A : Fin n → Finset H
  /-- The n families of sets B_i -/
  B : Fin n → Finset H
  /-- Each sumset A_i + B_i is direct -/
  direct : ∀ i, IsDirectSumset (A i) (B i)
  /-- Disjointness: A_i + B_i is disjoint from A_j + B_k when (i,k) ≠ (j,k) but specifically j ≠ k -/
  disjoint : ∀ i j k, j ≠ k → Disjoint (finsetSumset (A i) (B i)) (finsetSumset (A j) (B k))

/-- The asymptotic condition on group size: |H| should be n^{2+o(1)}.
    We express this as: for any ε > 0, |H| ≤ n^{2+ε} for large enough n. -/
def GroupSizeCondition (groupSize : ℕ → ℕ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, (groupSize n : ℝ) ≤ (n : ℝ) ^ (2 + ε)

/-- The asymptotic condition on product sizes: |A_i||B_i| ≥ n^{2-o(1)}.
    We express this as: for any ε > 0, |A_i||B_i| ≥ n^{2-ε} for large enough n. -/
def ProductSizeCondition {H : Type*} [AddCommGroup H] [DecidableEq H] [Fintype H]
    (config : (n : ℕ) → SumsetConfiguration H n) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ i : Fin n,
    ((config n).A i).card * ((config n).B i).card ≥ (n : ℝ) ^ (2 - ε)

/--
The main question (Problem 36):

For arbitrarily large n, does there exist an abelian group H and a configuration
satisfying the required asymptotic conditions?

We formalize "for arbitrarily large n" as: for all N, there exists n ≥ N such that
a valid configuration exists.
-/
def GreenProblem36 : Prop :=
  ∃ (familyH : ℕ → Type*)
    (familyGroup : ∀ n, AddCommGroup (familyH n))
    (familyDec : ∀ n, DecidableEq (familyH n))
    (familyFintype : ∀ n, Fintype (familyH n)),
    -- Group size condition: |H_n| = n^{2+o(1)}
    (∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, (Fintype.card (familyH n) : ℝ) ≤ (n : ℝ) ^ (2 + ε)) ∧
    -- Existence of configurations for arbitrarily large n
    (∀ N : ℕ, ∃ n ≥ N,
      ∃ (config : @SumsetConfiguration (familyH n) (familyGroup n) (familyDec n) (familyFintype n) n),
        -- Product size condition: |A_i||B_i| ≥ n^{2-o(1)} for all i
        ∀ ε > 0, ∀ i : Fin n,
          (config.A i).card * (config.B i).card ≥ (n : ℝ) ^ (2 - ε))

/-- Alternative formulation: configurations exist for infinitely many n -/
def GreenProblem36' : Prop :=
  ∃ (ns : ℕ → ℕ) (_ : ∀ N, ∃ k, ns k ≥ N)
    (familyH : ℕ → Type*)
    (familyGroup : ∀ k, AddCommGroup (familyH k))
    (familyDec : ∀ k, DecidableEq (familyH k))
    (familyFintype : ∀ k, Fintype (familyH k))
    (configs : ∀ k, @SumsetConfiguration (familyH k) (familyGroup k) (familyDec k) (familyFintype k) (ns k)),
    -- Group size is n^{2+o(1)}
    (∀ ε > 0, ∃ K : ℕ, ∀ k ≥ K, (Fintype.card (familyH k) : ℝ) ≤ (ns k : ℝ) ^ (2 + ε)) ∧
    -- Product sizes are n^{2-o(1)}
    (∀ ε > 0, ∃ K : ℕ, ∀ k ≥ K, ∀ i : Fin (ns k),
      ((configs k).A i).card * ((configs k).B i).card ≥ (ns k : ℝ) ^ (2 - ε))

/-- The problem as stated is an open question. We mark it with sorry as we are
    formalizing the statement, not proving it. -/
theorem green_problem_36_statement : GreenProblem36 ↔ GreenProblem36' := by
  sorry

end Green36
