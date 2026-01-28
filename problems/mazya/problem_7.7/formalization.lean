/-
Problem 7.7. Existence of a well-posed boundary value problem for general
differential operators in Lp(Ω)

Hörmander (1955) showed the existence of a well-posed boundary value problem
for every differential operator with constant coefficients in an arbitrary
bounded domain. Equivalently, he proved the estimate
  ‖u‖_{L²(Ω)} ≤ C ‖L(D) u‖_{L²(Ω)},
where u is an arbitrary function in C₀^∞(Ω).

Problem: Does this hold with Lp(Ω) instead of L²(Ω)?

We formalize:
1. Smooth functions with compact support in a bounded domain
2. Linear differential operators with constant coefficients (abstractly)
3. The Hörmander-type Lp estimate
-/

import Mathlib

open scoped BigOperators ENNReal
open MeasureTheory Set

noncomputable section

namespace Mazya77

variable {n : ℕ}

/-- A multi-index for partial derivatives in n dimensions -/
abbrev MultiIndex (n : ℕ) := Fin n → ℕ

/-- The order of a multi-index |α| = α₁ + α₂ + ... + αₙ -/
def MultiIndex.order (α : MultiIndex n) : ℕ := ∑ i, α i

/-- A linear constant-coefficient differential operator.
    Abstractly represented as a map from smooth functions to smooth functions
    that satisfies certain properties. We axiomatize this rather than
    giving a concrete representation. -/
structure ConstCoeffDiffOp (n : ℕ) where
  /-- The order of the differential operator -/
  order : ℕ
  /-- The action of the operator on smooth functions -/
  apply : (EuclideanSpace ℝ (Fin n) → ℂ) → (EuclideanSpace ℝ (Fin n) → ℂ)
  /-- The operator is linear -/
  linear : ∀ (a b : ℂ) (f g : EuclideanSpace ℝ (Fin n) → ℂ),
    apply (fun x => a • f x + b • g x) = fun x => a • apply f x + b • apply g x

/-- A function is smooth (C^∞) -/
def IsSmooth (f : EuclideanSpace ℝ (Fin n) → ℂ) : Prop :=
  ContDiff ℝ ⊤ f

/-- A function has compact support contained in Ω -/
def HasCompactSupportIn (f : EuclideanSpace ℝ (Fin n) → ℂ)
    (Ω : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  HasCompactSupport f ∧ Function.support f ⊆ Ω

/-- The space of smooth functions with compact support in Ω, i.e., C₀^∞(Ω) -/
def SmoothCompactSupport (Ω : Set (EuclideanSpace ℝ (Fin n))) :
    Set (EuclideanSpace ℝ (Fin n) → ℂ) :=
  {f | IsSmooth f ∧ HasCompactSupportIn f Ω}

/-- The Hörmander L^p estimate for a differential operator:
    There exists C > 0 such that ‖u‖_{Lp} ≤ C ‖L(D)u‖_{Lp} for all u ∈ C₀^∞(Ω) -/
def HormanderLpEstimate (L : ConstCoeffDiffOp n)
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (p : ENNReal) : Prop :=
  ∃ C : ℝ, C > 0 ∧ ∀ u ∈ SmoothCompactSupport Ω,
    eLpNorm u p volume ≤ ENNReal.ofReal C * eLpNorm (L.apply u) p volume

/--
**Problem 7.7 (Maz'ya):**

Hörmander proved that for every constant-coefficient differential operator L(D)
and every bounded domain Ω, there exists C > 0 such that
  ‖u‖_{L²(Ω)} ≤ C ‖L(D)u‖_{L²(Ω)}
for all u ∈ C₀^∞(Ω).

The problem asks: Does this generalize to Lp for p ≠ 2?

Formally: For all n, bounded Ω, differential operators L, and 1 ≤ p ≤ ∞,
does the Hörmander Lp estimate hold?
-/
theorem problem_7_7 :
    (∀ (n : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin n)))
       (_ : Bornology.IsBounded Ω) (_ : IsOpen Ω)
       (L : ConstCoeffDiffOp n) (p : ENNReal) (_ : 1 ≤ p),
       HormanderLpEstimate L Ω p) ↔ True := by
  sorry

/-- Alternative formulation asking whether the answer is yes or no -/
theorem problem_7_7_decidable :
    (∀ (n : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin n)))
       (_ : Bornology.IsBounded Ω) (_ : IsOpen Ω)
       (L : ConstCoeffDiffOp n) (p : ENNReal) (_ : 1 ≤ p),
       HormanderLpEstimate L Ω p) ∨
    ¬(∀ (n : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin n)))
       (_ : Bornology.IsBounded Ω) (_ : IsOpen Ω)
       (L : ConstCoeffDiffOp n) (p : ENNReal) (_ : 1 ≤ p),
       HormanderLpEstimate L Ω p) := by
  sorry

end Mazya77
