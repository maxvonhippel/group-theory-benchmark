/-
Klee Problem K-13: Minimal Convex Sets of Visibility and Star-Shapedness

PROBLEM:
Suppose X is a compact subset of E^n such that each point of X lies in a unique
minimal convex set of visibility. Must X include a point of visibility?

DEFINITIONS (from problem statement):
- A point x of X is visible (in X) from the point p of X provided X contains
  the entire segment [x, p].
- The point p is a point of visibility of X provided each point of X is visible from p.
  (Alternatively, we say that X is starshaped from p.)
- A set of visibility is a subset V of X such that each point of X is visible from
  some point of V.
- U_x denotes the family of all convex sets of visibility which contain the point x.
- A minimal member of U_x is a convex set of visibility V containing x such that V
  contains no other member of U_x (no proper subset of V is also in U_x).
- The problem asks: if for each point x of X there is a unique minimal member of U_x,
  must X be starshaped from some point?
-/

import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Segment
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Compactness.Compact

open Set

variable {n : ℕ}

/-- Euclidean n-space -/
abbrev En (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- A point x ∈ X is visible from p ∈ X if the closed segment [x, p] is contained in X. -/
def IsVisibleFrom (X : Set (En n)) (x p : X) : Prop :=
  segment ℝ (x : En n) (p : En n) ⊆ X

/-- A point p ∈ X is a point of visibility if every point of X is visible from p.
    Equivalently, X is star-shaped from p. -/
def IsPointOfVisibility (X : Set (En n)) (p : X) : Prop :=
  ∀ x : X, IsVisibleFrom X x p

/-- A set of visibility V ⊆ X is a subset such that each point of X
    is visible from some point of V. -/
def IsSetOfVisibility (X : Set (En n)) (V : Set (En n)) : Prop :=
  V ⊆ X ∧ ∀ x ∈ X, ∃ p ∈ V, segment ℝ x p ⊆ X

/-- A convex set of visibility is a set of visibility that is also convex. -/
def IsConvexSetOfVisibility (X : Set (En n)) (V : Set (En n)) : Prop :=
  IsSetOfVisibility X V ∧ Convex ℝ V

/-- U_x is the family of all convex sets of visibility containing point x. -/
def ConvexVisibilitySetsContaining (X : Set (En n)) (x : En n) : Set (Set (En n)) :=
  { V | IsConvexSetOfVisibility X V ∧ x ∈ V }

/-- A minimal convex set of visibility containing x is a member of U_x
    that contains no other member of U_x. -/
def IsMinimalConvexVisibilitySet (X : Set (En n)) (x : En n) (V : Set (En n)) : Prop :=
  V ∈ ConvexVisibilitySetsContaining X x ∧
  ∀ W ∈ ConvexVisibilitySetsContaining X x, W ⊆ V → W = V

/-- Each point x ∈ X lies in a unique minimal convex set of visibility. -/
def HasUniqueMinimalConvexVisibilitySets (X : Set (En n)) : Prop :=
  ∀ x ∈ X, ∃! V, IsMinimalConvexVisibilitySet X x V

/-- X has a point of visibility (is star-shaped from some point). -/
def HasPointOfVisibility (X : Set (En n)) : Prop :=
  ∃ p : X, IsPointOfVisibility X p

/--
**Klee Problem K-13**: Suppose X is a compact subset of E^n such that each point
of X lies in a unique minimal convex set of visibility. Must X include a point of visibility?

This is an open problem. We formalize it as the implication that would need to be
proved or disproved.
-/
theorem klee_K13 (X : Set (En n)) (hX_compact : IsCompact X) (hX_nonempty : X.Nonempty)
    (hX_unique_minimal : HasUniqueMinimalConvexVisibilitySets X) :
    HasPointOfVisibility X := by
  sorry

/-- The contrapositive formulation: if a compact nonempty set X has no point of visibility,
    then some point of X must lie in either zero or multiple minimal convex sets of visibility. -/
theorem klee_K13_contrapositive (X : Set (En n)) (hX_compact : IsCompact X)
    (hX_nonempty : X.Nonempty) (hX_no_visibility : ¬HasPointOfVisibility X) :
    ¬HasUniqueMinimalConvexVisibilitySets X := by
  intro h
  exact hX_no_visibility (klee_K13 X hX_compact hX_nonempty h)

/-- Alternative formulation: Either the conjecture holds or there exists a counterexample. -/
theorem klee_K13_decidable :
    (∀ (n : ℕ) (X : Set (En n)), IsCompact X → X.Nonempty →
      HasUniqueMinimalConvexVisibilitySets X → HasPointOfVisibility X) ∨
    (∃ (n : ℕ) (X : Set (En n)), IsCompact X ∧ X.Nonempty ∧
      HasUniqueMinimalConvexVisibilitySets X ∧ ¬HasPointOfVisibility X) := by
  sorry
