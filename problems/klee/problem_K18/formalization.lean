/-
Klee Problem K18: Some Inequalities Connected with Simplexes

PROBLEM:
Suppose p is a point of an n-dimensional simplex S, and for 0 ≤ i ≤ n−1, let Di denote the sum
of the distances from p to the various i-dimensional faces of S. What relations among the
numbers Di must persist for all p and S as described? In particular, if n = 3 (so that S is a
tetrahedron) is it true that:

i)  D₀ > √(8D₂)  (D. K. Kazarinoff)?
ii) D₀ > D₁      (A. Shields)?
iii) D₁ > 2D₂    (N. D. Kazarinoff and A. Shields)?

Here we formalize the three specific conjectures for tetrahedra.
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Projection
import Mathlib.LinearAlgebra.AffineSpace.Simplex.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance

open Set AffineSubspace EuclideanGeometry

noncomputable section

/-- Euclidean 3-space -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- A tetrahedron is a 3-simplex in Euclidean 3-space. -/
abbrev Tetrahedron := Affine.Simplex ℝ E3 3

/-- The affine span of a subset of vertices of a simplex. -/
def simplexFaceAffineSpan (S : Tetrahedron) (fs : Finset (Fin 4)) : AffineSubspace ℝ E3 :=
  affineSpan ℝ (S.points '' ↑fs)

/-- Distance from a point to an affine subspace (using infimum distance). -/
def distToAffineSubspace (p : E3) (A : AffineSubspace ℝ E3) : ℝ :=
  Metric.infDist p A.carrier

/-- D₀ = sum of distances from p to the 4 vertices (0-dimensional faces). -/
def sumDistToVertices (S : Tetrahedron) (p : E3) : ℝ :=
  ∑ i : Fin 4, dist p (S.points i)

/-- The set of all edges (1-faces) of a tetrahedron.
    An edge is determined by a pair of distinct vertices.
    There are C(4,2) = 6 edges. -/
def tetrahedronEdges : Finset (Finset (Fin 4)) :=
  Finset.filter (fun fs => fs.card = 2) (Finset.univ.powerset)

/-- The set of all 2-faces (triangular faces) of a tetrahedron.
    A face is determined by 3 vertices.
    There are C(4,3) = 4 faces. -/
def tetrahedronFaces : Finset (Finset (Fin 4)) :=
  Finset.filter (fun fs => fs.card = 3) (Finset.univ.powerset)

/-- D₁ = sum of distances from p to the 6 edges (as affine lines). -/
def sumDistToEdges (S : Tetrahedron) (p : E3) : ℝ :=
  ∑ e ∈ tetrahedronEdges, distToAffineSubspace p (simplexFaceAffineSpan S e)

/-- D₂ = sum of distances from p to the 4 triangular faces (as affine planes). -/
def sumDistToFaces (S : Tetrahedron) (p : E3) : ℝ :=
  ∑ f ∈ tetrahedronFaces, distToAffineSubspace p (simplexFaceAffineSpan S f)

/-!
## The Three Conjectures of Klee Problem K18

For any tetrahedron S and any point p in the closed interior of S
(i.e., in the convex hull of its vertices):
-/

/-- Conjecture (i) by D.K. Kazarinoff: D₀ > √(8D₂) -/
theorem klee_K18_conjecture_i (S : Tetrahedron) (p : E3) (hp : p ∈ S.closedInterior) :
    sumDistToVertices S p > Real.sqrt (8 * sumDistToFaces S p) := by
  sorry

/-- Conjecture (ii) by A. Shields: D₀ > D₁ -/
theorem klee_K18_conjecture_ii (S : Tetrahedron) (p : E3) (hp : p ∈ S.closedInterior) :
    sumDistToVertices S p > sumDistToEdges S p := by
  sorry

/-- Conjecture (iii) by N.D. Kazarinoff and A. Shields: D₁ > 2D₂ -/
theorem klee_K18_conjecture_iii (S : Tetrahedron) (p : E3) (hp : p ∈ S.closedInterior) :
    sumDistToEdges S p > 2 * sumDistToFaces S p := by
  sorry

/-- Alternative formulation: At least one of the conjectures is true or all are open. -/
theorem klee_K18_main :
    (∀ (S : Tetrahedron) (p : E3), p ∈ S.closedInterior →
      sumDistToVertices S p > Real.sqrt (8 * sumDistToFaces S p)) ∨
    (∀ (S : Tetrahedron) (p : E3), p ∈ S.closedInterior →
      sumDistToVertices S p > sumDistToEdges S p) ∨
    (∀ (S : Tetrahedron) (p : E3), p ∈ S.closedInterior →
      sumDistToEdges S p > 2 * sumDistToFaces S p) ∨
    -- Or there exist counterexamples to some/all
    (∃ (S : Tetrahedron) (p : E3), p ∈ S.closedInterior ∧
      sumDistToVertices S p ≤ Real.sqrt (8 * sumDistToFaces S p)) := by
  sorry

end
