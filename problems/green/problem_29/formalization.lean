/-
Problem 29. Suppose that A is a K-approximate group (not necessarily abelian).
Is there S ⊂ A, |S| ≫ K^{-O(1)}|A|, with S^8 ⊂ A^4?

We formalize this as:
  There exist universal constants c > 0 and C > 0 such that for every group G,
  every K ≥ 1, and every finite K-approximate subgroup A of G, there exists
  S ⊆ A with |S| ≥ c · K^{-C} · |A| and S^8 ⊆ A^4.

Here S^8 denotes the 8-fold product set S·S·S·S·S·S·S·S, and A^4 denotes
the 4-fold product set A·A·A·A.
-/

import Mathlib

open scoped Pointwise

namespace Green29

/--
The conjecture: There exist universal constants c > 0 and C > 0 such that
for any group G and any finite K-approximate subgroup A of G, there exists
a subset S of A with:
1. |S| ≥ c · K^{-C} · |A|  (polynomial lower bound on the size of S)
2. S^8 ⊆ A^4              (the 8-fold product of S is contained in the 4-fold product of A)

Note: The problem asks whether such a polynomial bound exists. The known result
(by Sanders) gives |S| ≫_K |A| but without a polynomial bound in K.
-/
theorem approximate_group_dense_subset_conjecture :
    ∃ (c : ℝ) (C : ℝ), c > 0 ∧ C > 0 ∧
    ∀ (G : Type*) [Group G] [DecidableEq G] (K : ℝ) (A : Finset G),
      K ≥ 1 →
      IsApproximateSubgroup K (A : Set G) →
      ∃ S : Finset G, S ⊆ A ∧
        (S.card : ℝ) ≥ c * K ^ (-C) * A.card ∧
        (↑(S ^ 8) : Set G) ⊆ (↑(A ^ 4) : Set G) := by
  sorry

/--
Alternative formulation with the constants as parameters rather than existentially quantified.
This states: For specific constants c and C, the property holds.
-/
def HasPolynomialDenseSubset (c C : ℝ) : Prop :=
  c > 0 ∧ C > 0 ∧
  ∀ (G : Type*) [Group G] [DecidableEq G] (K : ℝ) (A : Finset G),
    K ≥ 1 →
    IsApproximateSubgroup K (A : Set G) →
    ∃ S : Finset G, S ⊆ A ∧
      (S.card : ℝ) ≥ c * K ^ (-C) * A.card ∧
      (↑(S ^ 8) : Set G) ⊆ (↑(A ^ 4) : Set G)

/-- The conjecture restated using the predicate -/
theorem approximate_group_conjecture' : ∃ c C : ℝ, HasPolynomialDenseSubset c C := by
  sorry

/-
Related question (Shachar Lovett):
Suppose A ⊂ F_2^n has density 1/3. Is there a set B with 4B := B + B + B + B ⊆ A + A,
and 4B has density at least 1/100 in F_2^n?

This is an additive combinatorics question in the vector space F_2^n.
-/

/-- The density of a finite set in a finite type -/
noncomputable def density {α : Type*} [Fintype α] (S : Finset α) : ℝ :=
  S.card / Fintype.card α

/-- Lovett's question formalized for F_2^n -/
theorem lovett_question (n : ℕ) (hn : n > 0) :
    ∀ A : Finset (Fin n → ZMod 2),
      density A ≥ 1/3 →
      ∃ B : Finset (Fin n → ZMod 2),
        -- 4B ⊆ A + A (where 4B = B + B + B + B in the additive notation)
        (↑((B + B + B + B : Finset (Fin n → ZMod 2))) : Set (Fin n → ZMod 2)) ⊆
          ↑(A + A : Finset (Fin n → ZMod 2)) ∧
        -- 4B has density at least 1/100
        density (B + B + B + B) ≥ 1/100 := by
  sorry

end Green29
