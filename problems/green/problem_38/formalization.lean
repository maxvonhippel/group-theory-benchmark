/-
Problem 38 (Shannon capacity of 7-cycle / additive combinatorics version)

What is the largest subset A ⊂ F₇ⁿ for which A − A intersects {−1, 0, 1}ⁿ only at 0?

This is known to be a notorious open problem (the Shannon capacity of the 7-cycle).
We formalize the known bounds:
- Lower bound: |A| ≥ (367^(1/5))ⁿ ≈ 3.2578ⁿ (from explicit constructions)
- Upper bound: |A| ≤ (7 cos(π/7)/(1 + cos(π/7)))ⁿ ≈ 3.3177ⁿ (Lovász theta function)

Since the exact maximum is unknown, we formalize:
1. The constraint defining valid sets A
2. The known asymptotic bounds
-/

import Mathlib

open Finset ZMod

/-- The "small difference set" in (ZMod 7)ⁿ consisting of vectors with entries in {-1, 0, 1}.
    In ZMod 7, -1 = 6, 0 = 0, 1 = 1. -/
def SmallDiffSet (n : ℕ) : Set (Fin n → ZMod 7) :=
  {v | ∀ i, v i = 0 ∨ v i = 1 ∨ v i = 6}

/-- The difference set A - A for a subset A of an additive group -/
def DifferenceSet {G : Type*} [AddGroup G] (A : Set G) : Set G :=
  {x | ∃ a b, a ∈ A ∧ b ∈ A ∧ x = a - b}

/-- A subset A of (ZMod 7)ⁿ is "Shannon-valid" if A - A intersects
    the small difference set {-1, 0, 1}ⁿ only at 0. -/
def ShannonValid (n : ℕ) (A : Set (Fin n → ZMod 7)) : Prop :=
  DifferenceSet A ∩ SmallDiffSet n = {0}

/-- The maximum cardinality of a Shannon-valid finite subset of (ZMod 7)ⁿ -/
noncomputable def MaxShannonCapacity (n : ℕ) : ℕ :=
  sSup {k | ∃ A : Finset (Fin n → ZMod 7), A.card = k ∧ ShannonValid n (A : Set (Fin n → ZMod 7))}

/-- The lower bound constant C₁ = 367^(1/5) -/
noncomputable def C₁ : ℝ := (367 : ℝ) ^ (1/5 : ℝ)

/-- The upper bound constant C₂ = 7 cos(π/7) / (1 + cos(π/7)) (Lovász theta) -/
noncomputable def C₂ : ℝ := 7 * Real.cos (Real.pi / 7) / (1 + Real.cos (Real.pi / 7))

/-- Lower bound: There exist Shannon-valid sets of size at least C₁ⁿ (asymptotically).
    More precisely: for all ε > 0, for sufficiently large n, there exists a Shannon-valid
    set A with |A| ≥ (C₁ - ε)ⁿ -/
theorem shannon_capacity_lower_bound :
    ∀ ε > 0, ∃ N, ∀ n ≥ N, ∃ A : Finset (Fin n → ZMod 7),
      ShannonValid n (A : Set (Fin n → ZMod 7)) ∧
      (A.card : ℝ) ≥ (C₁ - ε) ^ n := by
  sorry

/-- Upper bound (Lovász 1979): Every Shannon-valid set has size at most C₂ⁿ (asymptotically).
    More precisely: for all ε > 0, for sufficiently large n, every Shannon-valid
    set A has |A| ≤ (C₂ + ε)ⁿ -/
theorem shannon_capacity_upper_bound :
    ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ A : Finset (Fin n → ZMod 7),
      ShannonValid n (A : Set (Fin n → ZMod 7)) →
      (A.card : ℝ) ≤ (C₂ + ε) ^ n := by
  sorry

/-- The asymptotic growth rate of the maximum Shannon-valid set size.
    The "Shannon capacity" Θ(C₇) satisfies C₁ ≤ Θ(C₇) ≤ C₂,
    and determining its exact value is the open problem. -/
theorem shannon_capacity_bounds : C₁ ≤ C₂ := by
  sorry
