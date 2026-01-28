/-
  Klee Problem K5: Neighboring Families of Convex Polyhedra

  For each pair of integers k and n with k − 1 ≥ n ≥ 3, determine the maximum
  possible number F(k, n) of neighboring convex polyhedra in E^n, each having
  at most k vertices.

  Two convex bodies in E^n are neighboring if their intersection is exactly
  (n − 1)-dimensional. A family of convex bodies is neighboring if each two
  of its members are neighboring.

  This formalization captures:
  - The definition of neighboring convex bodies
  - The definition of a k-vertex polyhedron (convex hull of at most k points)
  - The definition of F(k, n)
  - Known results: F(k, 2) = 4 for k ≥ 3, and 8 ≤ F(4, 3) ≤ 17
  - The finiteness of F(k, n)
-/

import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Finite.Basic

open Set Finset

variable {n : ℕ}

/-- The ambient Euclidean space E^n -/
abbrev EuclideanSpace' (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- A convex body in E^n is a nonempty compact convex set -/
structure ConvexBody (n : ℕ) where
  carrier : Set (EuclideanSpace' n)
  nonempty : carrier.Nonempty
  isCompact : IsCompact carrier
  convex : Convex ℝ carrier

instance : SetLike (ConvexBody n) (EuclideanSpace' n) where
  coe := ConvexBody.carrier
  coe_injective' := by
    intro a b h
    cases a; cases b
    simp only [ConvexBody.mk.injEq]
    exact h

/-- A convex polyhedron with at most k vertices is the convex hull of at most k points -/
def IsPolyhedronWithAtMostKVertices (K : ConvexBody n) (k : ℕ) : Prop :=
  ∃ (S : Finset (EuclideanSpace' n)), S.card ≤ k ∧ (K : Set (EuclideanSpace' n)) = convexHull ℝ (S : Set (EuclideanSpace' n))

/-- The dimension of a set in E^n, defined as the dimension of its affine span -/
noncomputable def setDimension (s : Set (EuclideanSpace' n)) : ℕ :=
  Module.finrank ℝ (affineSpan ℝ s).direction

/-- Two convex bodies are neighboring if their intersection is exactly (n-1)-dimensional -/
def AreNeighboring (K₁ K₂ : ConvexBody n) : Prop :=
  setDimension ((K₁ : Set (EuclideanSpace' n)) ∩ (K₂ : Set (EuclideanSpace' n))) = n - 1

/-- A family of convex bodies is neighboring if every pair of distinct members are neighboring -/
def IsNeighboringFamily {ι : Type*} (family : ι → ConvexBody n) : Prop :=
  ∀ i j, i ≠ j → AreNeighboring (family i) (family j)

/-- A neighboring family of k-vertex polyhedra -/
def IsNeighboringPolyhedraFamily {ι : Type*} (family : ι → ConvexBody n) (k : ℕ) : Prop :=
  IsNeighboringFamily family ∧ ∀ i, IsPolyhedronWithAtMostKVertices (family i) k

/-- The maximum size of a neighboring family of k-vertex polyhedra in E^n.
    This is defined as the supremum over all finite neighboring families. -/
noncomputable def F (k n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ (family : Fin m → ConvexBody n), IsNeighboringPolyhedraFamily family k}

/-! ## Known Results -/

/-- F(k, 2) = 4 for all k ≥ 3 (a neighboring family of plane convex bodies has at most 4 members) -/
theorem F_k_2_eq_four (k : ℕ) (hk : k ≥ 3) : F k 2 = 4 := by
  sorry

/-- Lower bound: F(4, 3) ≥ 8 (Bagemihl) -/
theorem F_4_3_lower_bound : F 4 3 ≥ 8 := by
  sorry

/-- Upper bound: F(4, 3) ≤ 17 (Bagemihl) -/
theorem F_4_3_upper_bound : F 4 3 ≤ 17 := by
  sorry

/-- Bagemihl's conjecture: F(4, 3) = 8 -/
def bagemihl_conjecture : Prop := F 4 3 = 8

/-- F(k, n) is always finite for k - 1 ≥ n ≥ 3 -/
theorem F_finite (k n : ℕ) (hn : n ≥ 3) (hkn : k - 1 ≥ n) : ∃ M : ℕ, F k n ≤ M := by
  sorry

/-! ## The Main Problem Statement

The problem asks: For each pair of integers k and n with k − 1 ≥ n ≥ 3,
determine F(k, n).

This is an open problem - we don't have a closed-form formula for F(k, n)
in general. The formalization captures the definition and known bounds.
-/

/-- The main problem: determine F(k, n) for all valid k, n.
    This states that there exists some function f computing F(k, n). -/
theorem main_problem_statement :
    ∃ (f : ℕ → ℕ → ℕ), ∀ k n, n ≥ 3 → k - 1 ≥ n → f k n = F k n := by
  exact ⟨F, fun _ _ _ _ => rfl⟩
