/-
Problem 49. (Solved) The Polynomial Freiman-Ruzsa Conjecture (PFR)

Suppose that A ⊂ F₂ⁿ is a set with |A + A| ≤ K|A|. Is it true that A is covered
by K^O(1) translates of a subspace of size ≤ |A|?

This is known as Marton's conjecture or the 'Polynomial Freiman–Ruzsa conjecture'
(PFR) in finite fields. It was solved in 2023 by Gowers, Manners, Tao, and Green.

We formalize the precise statement:
- A ⊂ F₂ⁿ with small sumset doubling |A + A| ≤ K|A|
- A can be covered by at most K^C translates of some subspace H
- The subspace H has size |H| ≤ |A|
-/

import Mathlib

namespace Green49

open Finset Set Pointwise

variable (n : ℕ)

/-- The finite field F₂ⁿ as an additive group -/
abbrev F2n (n : ℕ) := Fin n → ZMod 2

instance : AddCommGroup (F2n n) := Pi.addCommGroup

/-- The sumset A + A -/
def sumset (A : Finset (F2n n)) : Finset (F2n n) :=
  (A ×ˢ A).image (fun p => p.1 + p.2)

/-- A has small doubling constant K if |A + A| ≤ K * |A| -/
def hasSmallDoublingConst (A : Finset (F2n n)) (K : ℝ) : Prop :=
  (sumset n A).card ≤ K * A.card

/-- An additive subgroup of F₂ⁿ (i.e., a subspace) -/
abbrev Subspace (n : ℕ) := AddSubgroup (F2n n)

/-- A translate (coset) of a subspace by an element g -/
def translate (H : Subspace n) (g : F2n n) : Set (F2n n) :=
  {x | ∃ h ∈ H, x = g + h}

/-- A set A is covered by at most k translates of H -/
def isCoveredByTranslates (A : Finset (F2n n)) (H : Subspace n) (k : ℕ) : Prop :=
  ∃ T : Finset (F2n n), T.card ≤ k ∧ (A : Set (F2n n)) ⊆ ⋃ g ∈ T, translate n H g

/-- A subspace has size at most m -/
def subspaceHasSizeAtMost (H : Subspace n) (m : ℕ) : Prop :=
  Nat.card H ≤ m

/--
**The Polynomial Freiman-Ruzsa Conjecture (PFR) for F₂ⁿ:**

There exists a universal constant C > 0 such that:
For any n and any finite set A ⊂ F₂ⁿ with |A + A| ≤ K|A|,
there exists a subspace H of F₂ⁿ such that:
1. |H| ≤ |A|
2. A is covered by at most K^C translates of H

This was proven by Gowers, Green, Manners, and Tao in 2023.
-/
theorem polynomial_freiman_ruzsa_conjecture :
    ∃ C : ℝ, C > 0 ∧
    ∀ (n : ℕ) (A : Finset (F2n n)) (K : ℝ),
      K ≥ 1 →
      A.Nonempty →
      hasSmallDoublingConst n A K →
      ∃ H : Subspace n,
        subspaceHasSizeAtMost n H A.card ∧
        isCoveredByTranslates n A H ⌈K ^ C⌉₊ := by
  sorry

/--
A weaker form that just asserts the existence of a polynomial bound.
For any fixed K, the number of cosets needed is bounded by some polynomial in K.
-/
theorem pfr_polynomial_bound :
    ∀ (n : ℕ) (A : Finset (F2n n)) (K : ℝ),
      K ≥ 1 →
      A.Nonempty →
      hasSmallDoublingConst n A K →
      ∃ H : Subspace n,
        subspaceHasSizeAtMost n H A.card ∧
        ∃ (k : ℕ), ∃ (C : ℝ), C > 0 ∧ k ≤ ⌈K ^ C⌉₊ ∧
        isCoveredByTranslates n A H k := by
  sorry

/--
The Ruzsa covering lemma - a key ingredient used in the proof.
If |A + B| ≤ K|B|, then A can be covered by at most K translates of B - B.
(This is already in Mathlib as `Set.ruzsa_covering_add`)
-/
theorem ruzsa_covering_for_F2n (A B : Finset (F2n n)) (K : ℝ) (hK : K ≥ 1)
    (hA : A.Nonempty) (hB : B.Nonempty)
    (h : ((A : Set (F2n n)) + (B : Set (F2n n))).ncard ≤ K * B.card) :
    ∃ F : Finset (F2n n), F.card ≤ ⌈K⌉₊ ∧
      (A : Set (F2n n)) ⊆ (F : Set (F2n n)) + ((B : Set (F2n n)) - (B : Set (F2n n))) := by
  sorry

/--
Alternative formulation using Mathlib's doubling constant σ[A].
-/
theorem pfr_via_doubling_const :
    ∃ C : ℝ, C > 0 ∧
    ∀ (n : ℕ) (A : Finset (F2n n)),
      A.Nonempty →
      ∃ H : Subspace n,
        subspaceHasSizeAtMost n H A.card ∧
        isCoveredByTranslates n A H ⌈(A.addConst A : ℝ) ^ C⌉₊ := by
  sorry

end Green49
