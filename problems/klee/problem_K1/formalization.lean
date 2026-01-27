/-
Klee's Problem K1: Double Normals of Convex Bodies

PROBLEM:
Must a convex body in Eⁿ admit at least n doubly normal chords?

A chord of a convex body C is a line segment determined by two boundary points p and q.
The chord is normal at p if C lies entirely on one side of the hyperplane through p
perpendicular to the chord. A chord is doubly normal if it is normal at both endpoints.
-/

import Mathlib.Analysis.Convex.Body
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Basic

open Set Metric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A chord of a convex body is determined by two boundary points. -/
structure Chord (C : ConvexBody E) where
  p : E
  q : E
  hp : p ∈ frontier (C : Set E)
  hq : q ∈ frontier (C : Set E)
  hne : p ≠ q

/-- The direction vector of a chord (from p to q). -/
def Chord.direction {C : ConvexBody E} (c : Chord C) : E := c.q - c.p

/-- A chord is normal at point p if the convex body lies entirely on one side of
    the hyperplane through p perpendicular to the chord direction.
    Specifically, for all x in C, ⟪x - p, q - p⟫ ≥ 0. -/
def Chord.isNormalAtP {C : ConvexBody E} (c : Chord C) : Prop :=
  ∀ x ∈ (C : Set E), inner (𝕜 := ℝ) (x - c.p) (c.q - c.p) ≥ 0

/-- A chord is normal at point q if the convex body lies entirely on one side of
    the hyperplane through q perpendicular to the chord direction.
    Specifically, for all x in C, ⟪x - q, p - q⟫ ≥ 0. -/
def Chord.isNormalAtQ {C : ConvexBody E} (c : Chord C) : Prop :=
  ∀ x ∈ (C : Set E), inner (𝕜 := ℝ) (x - c.q) (c.p - c.q) ≥ 0

/-- A chord is doubly normal if it is normal at both endpoints. -/
def Chord.isDoublyNormal {C : ConvexBody E} (c : Chord C) : Prop :=
  c.isNormalAtP ∧ c.isNormalAtQ

/-- The set of all doubly normal chords of a convex body. -/
def doublyNormalChords (C : ConvexBody E) : Set (Chord C) :=
  {c | c.isDoublyNormal}

/-- Klee's Problem K1: Every convex body in a finite-dimensional real inner product space
    of dimension n admits at least n doubly normal chords.

    Note: This is stated as a conjecture. The problem asks whether this is true,
    and it is known to hold under various regularity conditions on the boundary. -/
def KleeProblemK1 [FiniteDimensional ℝ E] : Prop :=
  ∀ C : ConvexBody E, (interior (C : Set E)).Nonempty →
    ∃ chords : Finset (Chord C), chords.card ≥ Module.finrank ℝ E ∧ ∀ c ∈ chords, c.isDoublyNormal

/-- Alternative formulation using cardinality of a set. -/
def KleeProblemK1' [FiniteDimensional ℝ E] : Prop :=
  ∀ C : ConvexBody E, (interior (C : Set E)).Nonempty →
    ∃ S : Finset (Chord C), S.card ≥ Module.finrank ℝ E ∧ ↑S ⊆ doublyNormalChords C

/-- A weaker version: there exists at least one doubly normal chord (this is known to be true). -/
theorem exists_doubly_normal_chord (C : ConvexBody E) [FiniteDimensional ℝ E]
    (hne : (interior (C : Set E)).Nonempty) :
    ∃ c : Chord C, c.isDoublyNormal := by
  sorry

/-- An even weaker version: the diameter chord (connecting the two farthest points)
    is doubly normal. This is mentioned in the problem statement as known. -/
theorem diameter_chord_is_doubly_normal (C : ConvexBody E) [FiniteDimensional ℝ E]
    (hne : (interior (C : Set E)).Nonempty) :
    ∃ c : Chord C, c.isDoublyNormal ∧
      ∀ c' : Chord C, dist c.p c.q ≥ dist c'.p c'.q := by
  sorry
