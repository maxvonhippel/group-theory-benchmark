/-
Klee Problem K7: Decomposition of Nonexposed Extreme Points

If C is a convex body in E^n, must the boundary of C contain a sequence J1, J2, . . . ,
of closed sets satisfying the following condition:
Each nonexposed extreme point p of C lies in some set Ji; further, for each Ji
containing p there are exposed points arbitrarily close to p which lie outside Ji.

This formalization defines the relevant concepts and states the problem.
-/

import Mathlib.Analysis.Convex.Body
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Topology.Closure
import Mathlib.Analysis.InnerProductSpace.PiL2

open Set Topology

variable {n : ℕ}

/-- Euclidean n-space -/
abbrev EuclideanSpace' (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- Nonexposed extreme points: extreme points that are not exposed -/
def nonexposedExtremePoints (C : Set (EuclideanSpace' n)) : Set (EuclideanSpace' n) :=
  extremePoints ℝ C \ exposedPoints ℝ C

/-- The property that a sequence of closed sets satisfies the condition in Problem K7:
    1. Each nonexposed extreme point lies in some Ji
    2. For each Ji containing a nonexposed extreme point p, there are exposed points
       arbitrarily close to p that lie outside Ji -/
def KleeK7Property (C : Set (EuclideanSpace' n)) (J : ℕ → Set (EuclideanSpace' n)) : Prop :=
  -- All Ji are closed subsets of the boundary of C
  (∀ i, IsClosed (J i)) ∧
  (∀ i, J i ⊆ frontier C) ∧
  -- Each nonexposed extreme point lies in some Ji
  (∀ p ∈ nonexposedExtremePoints C, ∃ i, p ∈ J i) ∧
  -- For each Ji containing a nonexposed extreme point p,
  -- there are exposed points arbitrarily close to p outside Ji
  (∀ p ∈ nonexposedExtremePoints C, ∀ i, p ∈ J i →
    ∀ ε > 0, ∃ q ∈ exposedPoints ℝ C, dist q p < ε ∧ q ∉ J i)

/-- Problem K7: Does every convex body in E^n have a sequence of closed sets
    in its boundary satisfying the Klee K7 property? -/
theorem klee_problem_K7 (C : ConvexBody (EuclideanSpace' n)) :
    ∃ J : ℕ → Set (EuclideanSpace' n), KleeK7Property (C : Set (EuclideanSpace' n)) J := by
  sorry
