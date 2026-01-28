/-
Problem 19 from Green's problem list (Solved)

What is C, the infimum of all exponents c for which the following is true,
uniformly for 0 < α < 1? Suppose that A ⊂ F_2^n × F_2^n is a set of density α.
Write N := 2^n. Then there is some d such that A contains ≫ α^c · N² corners
(x, y), (x, y + d), (x + d, y).

The answer is C = 4 (proven by Fox, Sah, Sawhney, Stoner, and Zhao, 2019).

This formalization captures the resolved statement that C = 4.
-/

import Mathlib

open Finset

/-- The vector space F_2^n represented as functions from Fin n to ZMod 2 -/
abbrev F2n (n : ℕ) := Fin n → ZMod 2

/-- A corner in A ⊂ F_2^n × F_2^n is a triple of points (x, y), (x, y + d), (x + d, y)
    all contained in A, where d ≠ 0 -/
def IsCornerInSet {n : ℕ} (A : Finset (F2n n × F2n n)) (x y d : F2n n) : Prop :=
  d ≠ 0 ∧ (x, y) ∈ A ∧ (x, y + d) ∈ A ∧ (x + d, y) ∈ A

instance {n : ℕ} (A : Finset (F2n n × F2n n)) (x y d : F2n n) :
    Decidable (IsCornerInSet A x y d) := by
  unfold IsCornerInSet
  infer_instance

/-- Count corners in a finite set -/
noncomputable def countCornersInSet {n : ℕ} (A : Finset (F2n n × F2n n)) : ℕ :=
  (Finset.univ.filter (fun (xyd : F2n n × F2n n × F2n n) =>
    let (x, y, d) := xyd
    IsCornerInSet A x y d)).card

/-- The density of a finite set A in F_2^n × F_2^n -/
noncomputable def densityInF2n {n : ℕ} (A : Finset (F2n n × F2n n)) : ℝ :=
  A.card / (2 ^ n : ℝ) ^ 2

/-- The property that exponent c works: for some constant K > 0, for all n sufficiently large,
    for any set A of density α, the number of corners is at least K · α^c · N² -/
def CornerExponentWorks (c : ℝ) : Prop :=
  ∃ K : ℝ, K > 0 ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ A : Finset (F2n n × F2n n),
    let α := densityInF2n A
    0 < α → α < 1 →
    (countCornersInSet A : ℝ) ≥ K * α ^ c * (2 ^ n : ℝ) ^ 2

/-
The main theorem: C = 4 is the infimum of exponents that work.
This means:
1. The exponent c = 4 works (upper bound)
2. No exponent c < 4 works (lower bound)
-/

/-- Part 1: c = 4 works -/
theorem corner_exponent_four_works : CornerExponentWorks 4 := by
  sorry

/-- Part 2: No exponent c < 4 works -/
theorem corner_exponent_below_four_fails : ∀ c : ℝ, c < 4 → ¬CornerExponentWorks c := by
  sorry

/-- The infimum characterization: C = 4 -/
theorem corner_exponent_infimum :
    IsGLB {c : ℝ | CornerExponentWorks c} 4 := by
  sorry
