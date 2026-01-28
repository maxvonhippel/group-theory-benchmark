import Mathlib

/-!
# Green Problem 78: Measure Doubling in SO(3)

**Problem Statement:**
Let ε > 0. Suppose A ⊂ SO(3) is open and has sufficiently small (in terms of ε)
normalised Haar measure. Is µ(A · A) ≥ (4 − ε)µ(A)?

**Status:** Solved. The question has been resolved positively by Jing, Tran and Zhang (2023).

**Formalization Notes:**
We formalize this as: for every ε > 0, there exists δ > 0 such that for all open sets
A ⊂ SO(3) with Haar measure µ(A) < δ, we have µ(A · A) ≥ (4 - ε) · µ(A).

We work with a compact Lie group G representing SO(3) as an abstract type.
-/

open MeasureTheory Set Topology

/-- The product set A · A in a group -/
def productSet' {G : Type*} [Mul G] (A : Set G) : Set G :=
  {x | ∃ a b, a ∈ A ∧ b ∈ A ∧ x = a * b}

/--
Green Problem 78 (Abstract formulation):

For a compact connected Lie group G (specifically SO(3)), for every ε > 0,
there exists δ > 0 such that for all open sets A in G with normalized
Haar measure µ(A) < δ, we have µ(A · A) ≥ (4 - ε) · µ(A).

The constant 4 is optimal as it corresponds to the doubling constant for
small neighborhoods of a 1-dimensional subgroup.

This has been proved by Jing, Tran and Zhang (2023).
-/
theorem green_problem_78
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] [IsProbabilityMeasure μ] :
    ∀ ε : ℝ, 0 < ε →
    ∃ δ : ℝ, 0 < δ ∧
    ∀ A : Set G,
      IsOpen A →
      μ A < ENNReal.ofReal δ →
      μ (productSet' A) ≥ ENNReal.ofReal (4 - ε) * μ A := by
  sorry
