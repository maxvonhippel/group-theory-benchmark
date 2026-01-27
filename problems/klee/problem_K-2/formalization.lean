/-
Problem K-2: Line Segments in the Boundary of a Convex Body

PROBLEM: Is there a convex body C in E^n such that every direction in E^n
is realized by some line segment in the boundary of C?

We formalize this as the conjecture that no such convex body exists, i.e.,
for any convex body, there is some direction not realized by any segment
in its boundary.
-/

import Mathlib.Analysis.Convex.Body
import Mathlib.Analysis.Convex.Segment
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Topology.Defs.Basic

open Set Metric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The unit sphere in E -/
def unitSphereK2 (E : Type*) [NormedAddCommGroup E] : Set E := Metric.sphere 0 1

/-- Two vectors are parallel if one is a nonzero scalar multiple of the other -/
def AreParallelK2 (v w : E) : Prop := ∃ (c : ℝ), c ≠ 0 ∧ v = c • w

/-- A non-degenerate line segment: the segment between two distinct points -/
structure LineSegmentK2 (E : Type*) [NormedAddCommGroup E] [Module ℝ E] where
  p : E
  q : E
  distinct : p ≠ q

/-- The set of points in a line segment -/
def LineSegmentK2.toSet [Module ℝ E] (S : LineSegmentK2 E) : Set E :=
  segment ℝ S.p S.q

/-- The direction vector of a line segment (q - p) -/
def LineSegmentK2.directionVector [Module ℝ E] (S : LineSegmentK2 E) : E := S.q - S.p

/-- A direction d is realized by a line segment S if d is parallel to the segment's direction -/
def DirectionRealizedBySegmentK2 [Module ℝ E] (d : E) (S : LineSegmentK2 E) : Prop :=
  AreParallelK2 d S.directionVector

/-- A line segment is contained in the boundary (frontier) of a set -/
def SegmentInBoundaryK2 [Module ℝ E] [TopologicalSpace E] (S : LineSegmentK2 E) (C : Set E) : Prop :=
  S.toSet ⊆ frontier C

/-- The set of directions realized by some segment in the boundary of C -/
def realizedDirectionsK2 [Module ℝ E] [TopologicalSpace E] (C : Set E) : Set E :=
  {d ∈ unitSphereK2 E | ∃ (S : LineSegmentK2 E), SegmentInBoundaryK2 S C ∧ DirectionRealizedBySegmentK2 d S}

/--
Problem K-2: Negative Answer Conjecture

The conjecture (suggested by the problem's context) is that for any convex body C
in a finite-dimensional normed space, the set of realized directions is a proper
subset of the unit sphere.

In other words, there does not exist a convex body such that every direction
is realized by some segment in its boundary.
-/
theorem klee_K2_conjecture [FiniteDimensional ℝ E] (hE : 1 < Module.finrank ℝ E)
    (C : Set E) (hConvex : Convex ℝ C) (hCompact : IsCompact C) (hNonempty : C.Nonempty) :
    realizedDirectionsK2 C ≠ unitSphereK2 E := by
  sorry

/--
Alternative formulation: The original question asks whether such a convex body EXISTS.
This theorem states that no such convex body exists.
-/
theorem klee_K2_no_all_directions_body [FiniteDimensional ℝ E] (hE : 1 < Module.finrank ℝ E) :
    ¬∃ (C : Set E), Convex ℝ C ∧ IsCompact C ∧ C.Nonempty ∧ realizedDirectionsK2 C = unitSphereK2 E := by
  sorry

/--
The set of realized directions is an F_σ set (countable union of closed sets).
This is mentioned in the problem statement.
-/
theorem realizedDirectionsK2_isFsigma [FiniteDimensional ℝ E]
    (C : Set E) (hConvex : Convex ℝ C) (hCompact : IsCompact C) :
    ∃ (F : ℕ → Set E), (∀ n, IsClosed (F n)) ∧ realizedDirectionsK2 C = ⋃ n, F n := by
  sorry

/--
For dimension 2, the set of realized directions is countable.
-/
theorem realizedDirectionsK2_countable_dim2
    (C : Set (EuclideanSpace ℝ (Fin 2)))
    (hConvex : Convex ℝ C) (hCompact : IsCompact C) :
    (realizedDirectionsK2 C).Countable := by
  sorry

/--
McMinn's theorem (1960): For dimension 3, the set of realized directions
has measure zero and is of first category.
-/
theorem mcminn_theorem_dim3
    (C : Set (EuclideanSpace ℝ (Fin 3)))
    (hConvex : Convex ℝ C) (hCompact : IsCompact C) :
    -- First category (meager) in the unit sphere
    IsNowhereDense (realizedDirectionsK2 C) := by
  sorry
