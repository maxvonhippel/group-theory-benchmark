/-
Problem 6. Fix an integer d. What is the largest sum-free subset of [N]^d?

A subset S of an additive structure is sum-free if for all x, y ∈ S, x + y ∉ S.
[N]^d denotes the d-dimensional cube {1, 2, ..., N}^d.

We formalize:
1. The definition of sum-free subsets
2. The function f_d(N) = maximum size of sum-free subset of [N]^d
3. The known result that c_1 = 1/2 (where c_d = lim sup N^{-d} f_d(N))
-/

import Mathlib

open scoped BigOperators

namespace Green6

/-- A set S is sum-free if for all x, y ∈ S, x + y ∉ S -/
def IsSumFree {α : Type*} [Add α] (S : Set α) : Prop :=
  ∀ x y, x ∈ S → y ∈ S → x + y ∉ S

/-- Sum-free property for Finsets (via coercion to Set) -/
def Finset.IsSumFree' {α : Type*} [Add α] (S : Finset α) : Prop :=
  IsSumFree (S : Set α)

/-- The 1-dimensional case: [N] = {1, ..., N} -/
def interval (N : ℕ) : Finset ℕ := Finset.Icc 1 N

/-- f_1(N) for the 1-dimensional case: max cardinality of sum-free subset of [N] -/
noncomputable def f₁ (N : ℕ) : ℕ :=
  sSup {k | ∃ S : Finset ℕ, S ⊆ interval N ∧ IsSumFree (S : Set ℕ) ∧ S.card = k}

/-- The upper half of an interval is sum-free: {⌊N/2⌋ + 1, ..., N} -/
def upperHalf (N : ℕ) : Finset ℕ :=
  Finset.Icc (N / 2 + 1) N

/-- Upper half is sum-free: if x, y > N/2, then x + y > N -/
theorem upperHalf_sumFree (N : ℕ) : IsSumFree (upperHalf N : Set ℕ) := by
  intro x y hx hy hxy
  simp only [upperHalf, Finset.coe_Icc, Set.mem_Icc] at hx hy hxy
  omega

/-- The cardinality of the upper half -/
theorem upperHalf_card (N : ℕ) : (upperHalf N).card = N - N / 2 := by
  simp only [upperHalf, Nat.card_Icc]
  omega

/-- Upper half is a subset of [N] -/
theorem upperHalf_subset (N : ℕ) : upperHalf N ⊆ interval N := by
  intro x hx
  simp only [upperHalf, interval, Finset.mem_Icc] at hx ⊢
  omega

/-- Main theorem (d=1): The maximum sum-free subset of [N] has size approximately N/2.
    More precisely, f_1(N) = ⌈N/2⌉ -/
theorem f₁_eq (N : ℕ) (hN : N > 0) : f₁ N = (N + 1) / 2 := by
  sorry

/-- The asymptotic density c_1 = 1/2 -/
theorem c₁_eq_half :
    Filter.Tendsto (fun N => (f₁ N : ℚ) / N) Filter.atTop (nhds (1/2 : ℚ)) := by
  sorry

/-
For the d-dimensional case, we work with functions Fin d → ℕ representing points in ℤ^d.
Since Fin d → ℕ is not a Fintype, we define the cube differently.
-/

/-- The d-dimensional cube [N]^d as a set -/
def cubeSet (d N : ℕ) : Set (Fin d → ℕ) :=
  {v | ∀ i, 1 ≤ v i ∧ v i ≤ N}

/-- f_d(N) is the supremum of cardinalities of finite sum-free subsets of [N]^d -/
noncomputable def f (d N : ℕ) : ℕ :=
  sSup {k | ∃ S : Finset (Fin d → ℕ), (∀ v ∈ S, ∀ i, 1 ≤ v i ∧ v i ≤ N) ∧
            IsSumFree (S : Set (Fin d → ℕ)) ∧ S.card = k}

/-- For d = 2, Elsholtz and Rackham showed c_2 = 3/5 -/
theorem c₂_eq_three_fifths :
    Filter.Tendsto (fun N => (f 2 N : ℚ) / (N^2 : ℕ)) Filter.atTop (nhds (3/5 : ℚ)) := by
  sorry

/-- A 'slice' in [N]^d is the set of points where the coordinate sum is in [u, 2u) -/
def sliceSet (d N u : ℕ) : Set (Fin d → ℕ) :=
  {v ∈ cubeSet d N | u ≤ ∑ i, v i ∧ ∑ i, v i < 2 * u}

/-- Slices are sum-free: if x, y have coordinate sums in [u, 2u), then x + y has sum in [2u, 4u) -/
theorem sliceSet_sumFree (d N u : ℕ) : IsSumFree (sliceSet d N u) := by
  intro x y hx hy hxy
  simp only [sliceSet, cubeSet, Set.mem_setOf_eq] at hx hy hxy
  -- The sum of x + y has coordinate sum = (sum of x) + (sum of y) ≥ 2u
  have key : ∑ i, (x + y) i = ∑ i, x i + ∑ i, y i := by
    simp only [Pi.add_apply, Finset.sum_add_distrib]
  have hxy_sum := hxy.2
  rw [key] at hxy_sum
  omega

/-- The conjecture: for each d, there exists a constant c_d such that
    f_d(N) ~ c_d * N^d as N → ∞ -/
theorem exists_asymptotic_density (d : ℕ) (hd : d > 0) :
    ∃ c : ℚ, c > 0 ∧
    Filter.Tendsto (fun N => (f d N : ℚ) / (N^d : ℕ)) Filter.atTop (nhds c) := by
  sorry

/-- For d = 1, c_1 = 1/2 -/
theorem c_one_eq_half :
    Filter.Tendsto (fun N => (f 1 N : ℚ) / N) Filter.atTop (nhds (1/2 : ℚ)) := by
  sorry

end Green6
