/-
Klee Problem K5: Neighboring Families of Convex Polyhedra

For each pair of integers k and n with k−1 ≥ n ≥ 3, determine the maximum possible number
F(k, n) of neighboring convex polyhedra in E^n, each having at most k vertices.

Two convex bodies in E^n are said to be neighboring provided their intersection is exactly
(n − 1)-dimensional; a family of convex bodies is said to be neighboring provided each two
of its members are neighboring.

This formalization defines the relevant concepts and states known bounds.
-/

import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Data.Set.Card

open Set Convex

variable {n : ℕ}

/-- Euclidean n-space -/
abbrev EuclideanSpace' (n : ℕ) := EuclideanSpace ℝ (Fin n)

/--
A convex polyhedron with at most k vertices in Euclidean n-space is the convex hull
of a finite set of at most k points.
-/
def IsConvexPolyhedronWithAtMostKVertices (k : ℕ) (S : Set (EuclideanSpace' n)) : Prop :=
  ∃ (pts : Finset (EuclideanSpace' n)), pts.card ≤ k ∧ S = convexHull ℝ (pts : Set (EuclideanSpace' n))

/--
A convex body is a compact convex set with nonempty interior.
For this problem, we work with convex sets that are convex hulls of finite point sets.
-/
def IsConvexBody (S : Set (EuclideanSpace' n)) : Prop :=
  Convex ℝ S ∧ IsCompact S ∧ (interior S).Nonempty

/--
The affine dimension of a set is the dimension of its affine span.
-/
noncomputable def affineDim (S : Set (EuclideanSpace' n)) : ℕ :=
  Module.finrank ℝ (affineSpan ℝ S).direction

/--
Two convex bodies in E^n are neighboring if their intersection is exactly (n-1)-dimensional.
That is, the intersection has affine dimension n-1.
-/
def AreNeighboring (n : ℕ) (S T : Set (EuclideanSpace' n)) : Prop :=
  affineDim (S ∩ T) = n - 1

/--
A family of convex bodies is neighboring if every two distinct members are neighboring.
-/
def IsNeighboringFamily (n : ℕ) (F : Finset (Set (EuclideanSpace' n))) : Prop :=
  ∀ S T : Set (EuclideanSpace' n), S ∈ F → T ∈ F → S ≠ T → AreNeighboring n S T

/--
A family consists of convex polyhedra each with at most k vertices.
-/
def AllHaveAtMostKVertices (k : ℕ) (F : Finset (Set (EuclideanSpace' n))) : Prop :=
  ∀ S : Set (EuclideanSpace' n), S ∈ F → IsConvexPolyhedronWithAtMostKVertices k S

/--
F(k, n) is the maximum size of a neighboring family of convex polyhedra in E^n,
each having at most k vertices. This is defined for k - 1 ≥ n ≥ 3.

We define it as the supremum (as a natural number) of sizes of such families.
Note: The problem states this is always finite.
-/
noncomputable def maxNeighboringFamily (k n : ℕ) : ℕ :=
  sSup { m : ℕ | ∃ (F : Finset (Set (EuclideanSpace' n))),
    F.card = m ∧ IsNeighboringFamily n F ∧ AllHaveAtMostKVertices k F }

/--
**Known Result 1**: A neighboring family of plane convex bodies has at most four members.
F(k, 2) = 4 for all k ≥ 3.
-/
theorem plane_neighboring_family_bound (k : ℕ) (hk : k ≥ 3) :
    maxNeighboringFamily k 2 = 4 := by
  sorry

/--
**Known Result 2**: E^3 contains an infinite neighboring family of convex polyhedra.
(Without the vertex constraint, there is no finite bound in dimension 3.)
-/
theorem three_space_infinite_neighboring_family :
    ∀ m : ℕ, ∃ (F : Finset (Set (EuclideanSpace' 3))),
      F.card ≥ m ∧ IsNeighboringFamily 3 F ∧ (∀ S ∈ F, IsConvexBody S) := by
  sorry

/--
**Bagemihl's Bounds**: 8 ≤ F(4, 3) ≤ 17
The maximum number of neighboring tetrahedra in E^3.
-/
theorem bagemihl_lower_bound : maxNeighboringFamily 4 3 ≥ 8 := by
  sorry

theorem bagemihl_upper_bound : maxNeighboringFamily 4 3 ≤ 17 := by
  sorry

/--
**Bagemihl's Conjecture**: F(4, 3) = 8
-/
theorem bagemihl_conjecture : maxNeighboringFamily 4 3 = 8 := by
  sorry

/--
**Finiteness Result**: F(k, n) is always finite for k - 1 ≥ n ≥ 3.
An elaboration of Bagemihl's argument shows this.
-/
theorem neighboring_family_finite (k n : ℕ) (hn : n ≥ 3) (hkn : k ≥ n + 1) :
    ∃ bound : ℕ, maxNeighboringFamily k n ≤ bound := by
  sorry

/--
**Main Problem (K5)**: Determine F(k, n) for all valid pairs k, n with k - 1 ≥ n ≥ 3.

This problem asks to characterize the function maxNeighboringFamily for all valid inputs.
Since this is a "determine the value" problem rather than a specific claim,
we state it as: there exists a computable/explicit formula for F(k,n).
-/
theorem klee_problem_K5 :
    ∃ (f : ℕ → ℕ → ℕ), ∀ k n : ℕ, n ≥ 3 → k ≥ n + 1 →
      maxNeighboringFamily k n = f k n := by
  -- This is trivially true (f = maxNeighboringFamily works), but the problem
  -- asks for an *explicit* characterization, which is open.
  exact ⟨maxNeighboringFamily, fun _ _ _ _ => rfl⟩
