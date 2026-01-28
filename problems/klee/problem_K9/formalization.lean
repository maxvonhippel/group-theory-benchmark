/-
Klee's Problem K9: Expansive Homeomorphisms of the n-Cell

PROBLEM:
Can an n-dimensional convex body admit an expansive homeomorphism?

A homeomorphism T of a convex body C is expansive if there exists a positive number d
such that whenever x and y are distinct points of C, then for some n the distance
between T^n(x) and T^n(y) is at least d.

The problem notes that:
- For n=1 (intervals), no expansive homeomorphism exists (proven in the problem statement)
- For n ≥ 2, the problem is open
-/

import Mathlib.Analysis.Convex.Body
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

open Set Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A homeomorphism of a convex body C onto itself.
    This is a homeomorphism of the subtype (C : Set E) to itself. -/
abbrev ConvexBodyHomeomorph (C : ConvexBody E) := (C : Set E) ≃ₜ (C : Set E)

/-- The n-th iterate of a homeomorphism T. -/
def ConvexBodyHomeomorph.iterate {C : ConvexBody E} (T : ConvexBodyHomeomorph C) : ℕ → ConvexBodyHomeomorph C
  | 0 => Homeomorph.refl (C : Set E)
  | n + 1 => T.trans (iterate T n)

/-- A homeomorphism T of a convex body C is expansive if there exists a positive constant d
    such that for any two distinct points x, y in C, there exists some iterate n where
    the distance between T^n(x) and T^n(y) is at least d.

    This captures the idea that nearby orbits eventually separate by at least d. -/
def IsExpansive {C : ConvexBody E} (T : ConvexBodyHomeomorph C) : Prop :=
  ∃ d : ℝ, d > 0 ∧ ∀ x y : (C : Set E), x ≠ y →
    ∃ n : ℕ, dist (T.iterate n x : E) (T.iterate n y : E) ≥ d

/-- A convex body is n-dimensional if it has nonempty interior.
    (An n-dimensional convex body in ℝⁿ is one with nonempty interior in the ambient space.) -/
def ConvexBody.isFullDimensional (C : ConvexBody E) : Prop :=
  (interior (C : Set E)).Nonempty

/-- Klee's Problem K9: Does there exist an n-dimensional convex body that admits
    an expansive homeomorphism?

    The problem asks whether any convex body with nonempty interior can have
    a homeomorphism onto itself that is expansive.

    This is formulated as an existential question (can such a thing exist?).
    The problem statement notes this is open for dimension ≥ 2. -/
def KleeProblemK9 : Prop :=
  ∃ (E : Type*) (_ : NormedAddCommGroup E) (_ : NormedSpace ℝ E),
    ∃ C : ConvexBody E, C.isFullDimensional ∧
      ∃ T : ConvexBodyHomeomorph C, IsExpansive T

/-- Alternative formulation: For a fixed vector space E, can any convex body
    with nonempty interior admit an expansive homeomorphism? -/
def KleeProblemK9' (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] : Prop :=
  ∃ C : ConvexBody E, C.isFullDimensional ∧
    ∃ T : ConvexBodyHomeomorph C, IsExpansive T

/-- The negative result for dimension 1: No 1-dimensional convex body (interval)
    admits an expansive homeomorphism.

    This is proven in the problem statement by analyzing fixed points and
    monotonicity of iterates. -/
theorem no_expansive_homeomorphism_dim_one :
    ∀ C : ConvexBody ℝ, C.isFullDimensional →
      ∀ T : ConvexBodyHomeomorph C, ¬IsExpansive T := by
  sorry

/-- The open question: For n ≥ 2, does there exist an n-dimensional convex body
    with an expansive homeomorphism? -/
theorem klee_K9_open_for_dim_ge_2 (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (h : Module.finrank ℝ E ≥ 2) :
    (∃ C : ConvexBody E, C.isFullDimensional ∧ ∃ T : ConvexBodyHomeomorph C, IsExpansive T) ∨
    (∀ C : ConvexBody E, C.isFullDimensional → ∀ T : ConvexBodyHomeomorph C, ¬IsExpansive T) := by
  sorry
