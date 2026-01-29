/-
Problem 4. (Solved) What is the largest product-free set in the alternating group An?

A product-free set S in a group G is a set where for all x, y, z ∈ S, xy ≠ z.

The problem asks for the asymptotic behavior of the maximum size of a product-free
subset of the alternating group An as n → ∞.

Key results:
- Ed Crane showed there exist product-free sets of density ~n^(-1/2)
- Eberhard showed all product-free sets have density ≤ O(n^(-1/2) * (log n)^(7/2))
- Keevash, Lifschiz and Minzer (2022) proved the optimal bound is Θ(n^(-1/2))
-/

import Mathlib

open Equiv.Perm

namespace Green4

/-- A subset S of a group G is product-free if for all x, y, z ∈ S, we have xy ≠ z -/
def IsProductFree {G : Type*} [Group G] (S : Set G) : Prop :=
  ∀ x y z, x ∈ S → y ∈ S → z ∈ S → x * y ≠ z

/-- The alternating group on Fin n -/
abbrev Alt (n : ℕ) := alternatingGroup (Fin n)

/-- The cardinality of the alternating group An is n!/2 for n ≥ 2 -/
theorem alt_card (n : ℕ) (hn : n ≥ 2) :
    Fintype.card (Alt n) = Nat.factorial n / 2 := by
  sorry

/-- For the alternating group An, Crane's construction gives a product-free set
    of size approximately n!/2 * n^(-1/2), i.e., density roughly n^(-1/2).
    Specifically, he constructs a set S of all even permutations σ where
    σ(1) ∈ {2,...,m} and σ(2),...,σ(m) ∈ {m+1,...,n} for m ∼ √n -/
theorem crane_lower_bound (n : ℕ) (hn : n ≥ 2) :
    ∃ (S : Finset (Alt n)), IsProductFree (S : Set (Alt n)) ∧
    (S.card : ℝ) ≥ (Nat.factorial n : ℝ) / (2 * Real.sqrt n) / 2 := by
  sorry

/-- Eberhard's upper bound: any product-free subset of An has density
    at most C * n^(-1/2) * (log n)^(7/2) for some constant C -/
theorem eberhard_upper_bound :
    ∃ (C : ℝ), C > 0 ∧ ∀ (n : ℕ), n ≥ 2 →
    ∀ (S : Finset (Alt n)), IsProductFree (S : Set (Alt n)) →
    (S.card : ℝ) ≤ C * (Nat.factorial n / 2 : ℝ) * (n : ℝ)⁻¹ * (Real.log n)^(7/2 : ℝ) := by
  sorry

/-- The main result (Keevash-Lifschitz-Minzer 2022): The maximum product-free set
    in An has size Θ(|An| / √n).
    More precisely, there exist constants c, C > 0 such that the maximum
    product-free subset of An has size between c·n!/√n and C·n!/√n -/
theorem keevash_lifschitz_minzer :
    ∃ (c C : ℝ), c > 0 ∧ C > 0 ∧ ∀ (n : ℕ), n ≥ 2 →
    -- Lower bound: there exists a product-free set of size at least c * |An| / √n
    (∃ (S : Finset (Alt n)), IsProductFree (S : Set (Alt n)) ∧
      (S.card : ℝ) ≥ c * (Nat.factorial n / 2 : ℝ) / Real.sqrt n) ∧
    -- Upper bound: every product-free set has size at most C * |An| / √n
    (∀ (S : Finset (Alt n)), IsProductFree (S : Set (Alt n)) →
      (S.card : ℝ) ≤ C * (Nat.factorial n / 2 : ℝ) / Real.sqrt n) := by
  sorry

/-- The density function: ratio of product-free set size to |An| -/
noncomputable def maxProductFreeDensity (n : ℕ) : ℝ :=
  if _h : n ≥ 2 then
    sSup {(S.card : ℝ) / (Fintype.card (Alt n) : ℝ) |
      (S : Finset (Alt n)) (_hS : IsProductFree (S : Set (Alt n)))}
  else 0

/-- The asymptotic density is Θ(1/√n) -/
theorem asymptotic_density :
    ∃ (c C : ℝ), c > 0 ∧ C > 0 ∧
    ∀ᶠ (n : ℕ) in Filter.atTop, c / Real.sqrt n ≤ maxProductFreeDensity n ∧
                          maxProductFreeDensity n ≤ C / Real.sqrt n := by
  sorry

end Green4
