import Mathlib

/-!
# Green's Problem 14: 2-colour van der Waerden numbers

Define the 2-colour van der Waerden numbers W(k, r) to be the least quantities such that
if {1, . . . , W(k, r)} is coloured red and blue then there is either a red k-term
arithmetic progression or a blue r-term arithmetic progression.

Questions:
1. Is W(k, r) a polynomial in r, for fixed k?
2. Is W(3, r) ≪ r²?

UPDATE (Solved): Both questions are resolved in the NEGATIVE.
- Green (2021) proved W(3, r) ≫ exp(c(log r)^{4/3 - o(1)})
- Hunter improved this to W(3, r) ≫ exp(c(log r)^{2 - o(1)})
- Kelley-Meka showed W(3, r) ≪ exp(C(log r)^C) for some constant C

This shows W(k, r) is NOT polynomial in r even for k = 3.
-/

open Finset

/-- A k-term arithmetic progression starting at a with common difference d -/
def ArithProgression (a d : ℕ) (k : ℕ) : Finset ℕ :=
  (Finset.range k).image (fun i => a + i * d)

/-- A k-term AP contained in {1, ..., n} with positive common difference -/
def APInRange (a d k n : ℕ) : Prop :=
  d > 0 ∧ ∀ i < k, 1 ≤ a + i * d ∧ a + i * d ≤ n

/-- A coloring has a monochromatic red k-term AP -/
def HasRedAP (c : ℕ → Bool) (k n : ℕ) : Prop :=
  ∃ a d : ℕ, APInRange a d k n ∧ ∀ i < k, c (a + i * d) = true

/-- A coloring has a monochromatic blue r-term AP -/
def HasBlueAP (c : ℕ → Bool) (r n : ℕ) : Prop :=
  ∃ a d : ℕ, APInRange a d r n ∧ ∀ i < r, c (a + i * d) = false

/-- Property that makes n a valid "witness" for W(k, r):
    every 2-coloring of {1,...,n} has either a red k-AP or a blue r-AP -/
def VDWProperty (k r n : ℕ) : Prop :=
  ∀ c : ℕ → Bool, HasRedAP c k n ∨ HasBlueAP c r n

/-- The van der Waerden number W(k, r) exists and is the minimum n
    such that every 2-coloring of {1,...,n} contains either a red k-AP or blue r-AP -/
def VDWNumberExists (k r : ℕ) : Prop :=
  k ≥ 1 → r ≥ 1 → ∃ n : ℕ, VDWProperty k r n

/-- Van der Waerden's theorem: W(k, r) exists for all k, r ≥ 1 -/
theorem vanDerWaerden_exists (k r : ℕ) (hk : k ≥ 1) (hr : r ≥ 1) :
    ∃ n : ℕ, VDWProperty k r n := by
  sorry

/-- The set of n satisfying the VDW property is nonempty (for k, r ≥ 1) -/
theorem vdw_set_nonempty (k r : ℕ) (hk : k ≥ 1) (hr : r ≥ 1) :
    { n : ℕ | VDWProperty k r n }.Nonempty := by
  obtain ⟨n, hn⟩ := vanDerWaerden_exists k r hk hr
  exact ⟨n, hn⟩

/-- The van der Waerden number W(k, r) defined as the minimum n such that
    VDWProperty k r n holds. We use sInf for sets of naturals. -/
noncomputable def W (k r : ℕ) : ℕ :=
  sInf { n : ℕ | VDWProperty k r n }

/-- W(k, r) satisfies the defining property when k, r ≥ 1 -/
theorem W_satisfies_property (k r : ℕ) (hk : k ≥ 1) (hr : r ≥ 1) :
    VDWProperty k r (W k r) := by
  sorry

/-- W(k, r) is minimal -/
theorem W_minimal (k r n : ℕ) (hk : k ≥ 1) (hr : r ≥ 1) (hn : n < W k r) :
    ¬VDWProperty k r n := by
  sorry

/-! ## The resolved problem: W(k, r) is NOT polynomial in r

The main result (Green 2021, improved by Hunter):
W(3, r) grows faster than any polynomial in r.

Specifically:
- Lower bound: W(3, r) ≫ exp(c(log r)^{2-o(1)}) (Hunter)
- Upper bound: W(3, r) ≪ exp(C(log r)^C) (Kelley-Meka)

This proves that W(k, r) is NOT polynomial in r, even for k = 3.
-/

/-- A function f : ℕ → ℕ is eventually dominated by polynomials if
    for some polynomial p, f(n) ≤ p(n) for all sufficiently large n -/
def EventuallyPolynomialBounded (f : ℕ → ℕ) : Prop :=
  ∃ (c : ℕ) (d : ℕ), ∀ᶠ n in Filter.atTop, f n ≤ c * n ^ d + c

/-- W(3, r) is NOT polynomial in r.
    This is the main negative resolution of Problem 14. -/
theorem W3_not_polynomial_in_r :
    ¬EventuallyPolynomialBounded (fun r => W 3 r) := by
  sorry

/-- Green's lower bound (2021): W(3, r) ≫ exp(c(log r)^{4/3 - o(1)})
    We state a simplified version: W(3, r) grows faster than any polynomial -/
theorem green_lower_bound_W3 :
    ∀ (d : ℕ), ∀ (c : ℕ), ∀ᶠ r in Filter.atTop, W 3 r > c * r ^ d := by
  sorry

/-- Hunter's improved lower bound: W(3, r) ≫ exp(c(log r)^{2 - o(1)})
    This is closer to the truth. We state a consequence: super-polynomial growth -/
theorem hunter_lower_bound_W3 :
    ∀ p : Polynomial ℕ, ∀ᶠ r in Filter.atTop, W 3 r > p.eval r := by
  sorry

/-- Kelley-Meka upper bound: W(3, r) ≪ exp(C(log r)^C) for some constant C
    This shows W(3, r) is at most quasi-polynomial in a weak sense -/
theorem kelley_meka_upper_bound :
    ∃ (C : ℕ), ∀ᶠ r in Filter.atTop, (W 3 r : ℝ) ≤ Real.exp (C * (Real.log r) ^ C) := by
  sorry

/-- For general k: W(k, r) is not polynomial in r for any fixed k ≥ 3 -/
theorem Wk_not_polynomial_in_r (k : ℕ) (hk : k ≥ 3) :
    ¬EventuallyPolynomialBounded (fun r => W k r) := by
  sorry

/-- Known exact values: W(3, r) for small r
    These are computed values from numerical work -/
theorem W3_small_values :
    W 3 3 = 9 ∧ W 3 4 = 18 ∧ W 3 5 = 22 ∧ W 3 6 = 32 ∧ W 3 7 = 46 := by
  sorry

/-- The counterexample to W(3, r) ≤ r²: first occurs at r = 24 -/
theorem W3_exceeds_square_at_24 : W 3 24 > 24 ^ 2 := by
  sorry
