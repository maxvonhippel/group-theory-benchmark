/-
Green's 100 Open Problems, Problem 28

Suppose that X, Y are two finitely-supported independent random variables taking integer values,
and such that X + Y is uniformly distributed on its range. Are X and Y themselves uniformly
distributed on their ranges?

This formalization expresses the problem as asking whether the following implication holds:
if X and Y are finitely-supported independent integer-valued random variables and X + Y is
uniform on its support, then X and Y are each uniform on their supports.
-/

import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

open scoped ENNReal MeasureTheory
open MeasureTheory ProbabilityTheory Set

noncomputable section

/--
A measure on ℤ has finite support if only finitely many integers have positive measure.
-/
def HasFiniteSupport (μ : Measure ℤ) : Prop :=
  {n : ℤ | μ {n} ≠ 0}.Finite

/--
The support of a measure on ℤ as a Finset, given that it has finite support.
-/
def supportFinset (μ : Measure ℤ) (h : HasFiniteSupport μ) : Finset ℤ :=
  h.toFinset

/--
A measure on ℤ with finite support is uniform on its support if it assigns
equal probability to each point in the support (probability 1/|S| for each point).
-/
def IsUniformOnSupport (μ : Measure ℤ) (h : HasFiniteSupport μ) : Prop :=
  let S := supportFinset μ h
  S.Nonempty ∧ ∀ n : ℤ, μ {n} = if n ∈ S then (S.card : ℝ≥0∞)⁻¹ else 0

/--
**Green Problem 28**: Suppose X, Y are finitely-supported independent integer-valued random
variables such that X + Y is uniformly distributed on its range. Are X and Y themselves
uniformly distributed on their ranges?

This formalizes the question as: does the following implication hold for ALL pairs (X, Y)?

Given:
- A probability space (Ω, ℙ)
- Measurable functions X, Y : Ω → ℤ
- The pushforward measures μX = ℙ ∘ X⁻¹ and μY = ℙ ∘ Y⁻¹ have finite support
- X and Y are independent
- The sum X + Y is uniform on its support (the set of integers with positive probability)

Conclude:
- X is uniform on its support AND Y is uniform on its support

The theorem below states this implication. A proof would confirm the positive answer;
a counterexample would refute it.
-/
theorem green_problem_28 :
    ∀ (Ω : Type*) [MeasurableSpace Ω] (ℙ : Measure Ω) [IsProbabilityMeasure ℙ]
      (X Y : Ω → ℤ) (hXm : Measurable X) (hYm : Measurable Y)
      (hFinX : HasFiniteSupport (Measure.map X ℙ))
      (hFinY : HasFiniteSupport (Measure.map Y ℙ))
      (hFinXY : HasFiniteSupport (Measure.map (fun ω => X ω + Y ω) ℙ))
      (hIndep : IndepFun X Y ℙ)
      (hUnifXY : IsUniformOnSupport (Measure.map (fun ω => X ω + Y ω) ℙ) hFinXY),
      IsUniformOnSupport (Measure.map X ℙ) hFinX ∧
      IsUniformOnSupport (Measure.map Y ℙ) hFinY := by
  sorry

end

