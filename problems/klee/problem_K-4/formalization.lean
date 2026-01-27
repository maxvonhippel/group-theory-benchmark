import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Klee Problem K-4: Farthest and Nearest Points in Hilbert Space

## Problem Statement

**Part 1:** Suppose X is a subset of Hilbert space H such that each point of H
admits a unique farthest point in X. Must X consist of a single point?

**Part 2:** Suppose Y is a subset of Hilbert space H such that each point of H
admits a unique nearest point in Y. Must Y be convex?
-/

open Set Metric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- A point `y ∈ X` is a farthest point in `X` from `x` if
    `dist x y ≥ dist x z` for all `z ∈ X`. -/
def IsFarthestPointIn (X : Set E) (x y : E) : Prop :=
  y ∈ X ∧ ∀ z ∈ X, dist x z ≤ dist x y

/-- A point `y ∈ Y` is a nearest point in `Y` from `x` if
    `dist x y ≤ dist x z` for all `z ∈ Y`. -/
def IsNearestPointIn (Y : Set E) (x y : E) : Prop :=
  y ∈ Y ∧ ∀ z ∈ Y, dist x y ≤ dist x z

/-- Every point in `H` admits a unique farthest point in `X`. -/
def HasUniqueFarthestPoints (X : Set E) : Prop :=
  ∀ x : E, ∃! y : E, IsFarthestPointIn X x y

/-- Every point in `H` admits a unique nearest point in `Y`. -/
def HasUniqueNearestPoints (Y : Set E) : Prop :=
  ∀ x : E, ∃! y : E, IsNearestPointIn Y x y

/-- **Klee Problem K-4, Part 1:**
    If every point of a real Hilbert space H admits a unique farthest point in X,
    must X consist of a single point? -/
theorem klee_K4_farthest_point (X : Set E) (hX : X.Nonempty)
    (h : HasUniqueFarthestPoints X) : X.Subsingleton := by
  sorry

/-- **Klee Problem K-4, Part 2:**
    If every point of a real Hilbert space H admits a unique nearest point in Y,
    must Y be convex? -/
theorem klee_K4_nearest_point (Y : Set E) (hY : Y.Nonempty)
    (h : HasUniqueNearestPoints Y) : Convex ℝ Y := by
  sorry
