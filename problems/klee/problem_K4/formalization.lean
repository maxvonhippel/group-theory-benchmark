import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Set.Subsingleton

/-!
# Problem K4

Suppose X is a subset of Hilbert space H such that each point of H admits a unique
farthest point in X. Must X consist of a single point?

## Formalization

We formalize this as a theorem: if X is a nonempty subset of a real Hilbert space H
such that every point in H has a unique farthest point in X, then X is a singleton.

The "farthest point" condition means: for each h ∈ H, there exists a unique x ∈ X
such that dist(h, x) = sup{dist(h, y) | y ∈ X}.
-/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- A point x ∈ X is a farthest point from h if it achieves the supremum distance. -/
def IsFarthestPoint (X : Set H) (h : H) (x : H) : Prop :=
  x ∈ X ∧ ∀ y ∈ X, dist h y ≤ dist h x

/-- Every point in H admits a unique farthest point in X. -/
def HasUniqueFarthestPoints (X : Set H) : Prop :=
  ∀ h : H, ∃! x, IsFarthestPoint X h x

/-- Problem K4: If every point in a Hilbert space H has a unique farthest point in X,
    must X be a singleton (or empty)? The problem implicitly assumes X is nonempty
    (otherwise the "unique farthest point" condition is vacuously impossible),
    so we ask: must X be a subsingleton? -/
theorem problem_K4 (X : Set H) (hX : HasUniqueFarthestPoints X) : X.Subsingleton := by
  sorry
