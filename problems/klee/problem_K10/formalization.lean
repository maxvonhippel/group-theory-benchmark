import Mathlib.Analysis.Convex.Body
import Mathlib.Analysis.Convex.Segment
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Basic

/-!
# Equichordal Points of Convex Bodies (Klee Problem K10)

## Problem Statement
Does there exist (for n ≥ 2) an n-dimensional convex body which has two equichordal points?

## Definitions
- A point p in the interior of a set C is an **equichordal point** if all chords of C
  passing through p have the same length.
- A **chord** through p is a maximal line segment contained in C that passes through p.

## Note
This problem was famously solved by Marek Rychlik in 1997, who proved that no such
convex body exists in dimension 2 (and hence in any dimension ≥ 2).
-/

open Set Metric

variable {n : ℕ} (hn : n ≥ 2)

/-- The type for n-dimensional Euclidean space -/
abbrev EuclideanN (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- A chord of a set C through point p is determined by two boundary points x and y
    such that p lies on the segment from x to y, and the segment is contained in C. -/
def IsChordThrough (C : Set (EuclideanN n)) (p x y : EuclideanN n) : Prop :=
  x ∈ frontier C ∧
  y ∈ frontier C ∧
  x ≠ y ∧
  p ∈ segment ℝ x y ∧
  segment ℝ x y ⊆ C

/-- The length of a chord from x to y -/
noncomputable def chordLength (x y : EuclideanN n) : ℝ := dist x y

/-- A point p is an equichordal point of C if:
    1. p is in the interior of C
    2. All chords through p have the same length -/
def IsEquichordal (C : Set (EuclideanN n)) (p : EuclideanN n) : Prop :=
  p ∈ interior C ∧
  ∃ L : ℝ, L > 0 ∧ ∀ x y : EuclideanN n,
    IsChordThrough C p x y → chordLength x y = L

/-- A convex body is a compact convex set with nonempty interior -/
def IsConvexBody (C : Set (EuclideanN n)) : Prop :=
  Convex ℝ C ∧ IsCompact C ∧ (interior C).Nonempty

/-- The main problem: Does there exist a convex body with two distinct equichordal points?
    This is formalized as the negation of the existence statement, since Rychlik proved
    no such body exists. -/
theorem no_two_equichordal_points :
    ∀ C : Set (EuclideanN n), IsConvexBody C →
    ∀ p q : EuclideanN n, IsEquichordal C p → IsEquichordal C q → p = q := by
  sorry

/-- Alternative formulation as the original question (existence) -/
def existsTwoEquichordalPoints (n : ℕ) : Prop :=
  ∃ C : Set (EuclideanN n), IsConvexBody C ∧
  ∃ p q : EuclideanN n, p ≠ q ∧ IsEquichordal C p ∧ IsEquichordal C q

/-- The answer to the problem is negative: no such convex body exists for n ≥ 2 -/
theorem answer_is_no (hn : n ≥ 2) : ¬ existsTwoEquichordalPoints n := by
  sorry
