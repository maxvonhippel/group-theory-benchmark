/-
Problem 69. Fix a number k. Let A ⊂ ℝ² be a set of n points, with no more than k on any line.
Suppose that, for at least δn² pairs of points (x, y) ∈ A × A, the line xy contains a third
point of A. Is there some cubic curve containing at least cn points of A, for some c = c(k, δ) > 0?

This is an open conjecture in combinatorial geometry relating the density of collinear
triples in a point set to the existence of large subsets on cubic curves.
-/

import Mathlib

namespace Green69

/-- Three points are collinear if they lie on a common line -/
def areCollinear (p q r : Fin 2 → ℝ) : Prop :=
  Collinear ℝ ({p, q, r} : Set (Fin 2 → ℝ))

/-- A set has at most k points on any line -/
def AtMostKOnAnyLine (A : Set (Fin 2 → ℝ)) (k : ℕ) : Prop :=
  ∀ (L : Set (Fin 2 → ℝ)),
    (∃ p q : Fin 2 → ℝ, p ≠ q ∧ L = {r | Collinear ℝ ({p, q, r} : Set (Fin 2 → ℝ))}) →
    (A ∩ L).ncard ≤ k

/-- A pair (x, y) from A × A has a third collinear point in A if there exists
    z ∈ A distinct from x and y such that x, y, z are collinear -/
def hasThirdCollinearPoint (A : Set (Fin 2 → ℝ)) (x y : Fin 2 → ℝ) : Prop :=
  ∃ z ∈ A, z ≠ x ∧ z ≠ y ∧ areCollinear x y z

/-- The set of pairs (x, y) ∈ A × A that have a third collinear point in A -/
def collinearPairs (A : Set (Fin 2 → ℝ)) : Set ((Fin 2 → ℝ) × (Fin 2 → ℝ)) :=
  {xy ∈ A ×ˢ A | hasThirdCollinearPoint A xy.1 xy.2}

/-- A cubic polynomial in two variables (total degree at most 3) -/
def IsCubicPolynomial (p : MvPolynomial (Fin 2) ℝ) : Prop :=
  p.totalDegree ≤ 3 ∧ p ≠ 0

/-- The zero set of a polynomial in ℝ² -/
def zeroSet (p : MvPolynomial (Fin 2) ℝ) : Set (Fin 2 → ℝ) :=
  {x | MvPolynomial.eval x p = 0}

/-- A cubic curve is the zero set of a non-zero polynomial of total degree at most 3 -/
def IsCubicCurve (C : Set (Fin 2 → ℝ)) : Prop :=
  ∃ p : MvPolynomial (Fin 2) ℝ, IsCubicPolynomial p ∧ C = zeroSet p

/-- Green's Conjecture (Problem 69):
    For any k ≥ 1 and δ > 0, there exists c = c(k, δ) > 0 such that:
    For any finite set A ⊂ ℝ² with n = |A| points, at most k on any line,
    if at least δn² pairs (x,y) ∈ A×A have a third collinear point in A,
    then there exists a cubic curve containing at least cn points of A. -/
theorem green_conjecture_69 :
    ∀ (k : ℕ), k ≥ 1 →
    ∀ (δ : ℝ), δ > 0 →
    ∃ (c : ℝ), c > 0 ∧
      ∀ (A : Set (Fin 2 → ℝ)), A.Finite →
        let n := A.ncard
        AtMostKOnAnyLine A k →
        ((collinearPairs A).ncard : ℝ) ≥ δ * (n : ℝ)^2 →
        ∃ (C : Set (Fin 2 → ℝ)), IsCubicCurve C ∧
          ((A ∩ C).ncard : ℝ) ≥ c * (n : ℝ) := by
  sorry

/-- Alternative formulation emphasizing the dependence of c on k and δ -/
theorem green_conjecture_69_explicit :
    ∃ (f : ℕ → ℝ → ℝ), (∀ k δ, k ≥ 1 → δ > 0 → f k δ > 0) ∧
      ∀ (k : ℕ), k ≥ 1 →
      ∀ (δ : ℝ), δ > 0 →
      ∀ (A : Set (Fin 2 → ℝ)), A.Finite →
        let n := A.ncard
        let c := f k δ
        AtMostKOnAnyLine A k →
        ((collinearPairs A).ncard : ℝ) ≥ δ * (n : ℝ)^2 →
        ∃ (C : Set (Fin 2 → ℝ)), IsCubicCurve C ∧
          ((A ∩ C).ncard : ℝ) ≥ c * (n : ℝ) := by
  sorry

/-- Elekes-Szabó's weaker conjecture mentioned in the comments:
    If A has cn² collinear triples (no k-on-a-line assumption), do some 10 points
    of A lie on a cubic curve?
    (Note: there is a cubic curve through any 9 points) -/
theorem elekes_szabo_weak_conjecture :
    ∃ (c₀ : ℝ), c₀ > 0 ∧
    ∀ (A : Set (Fin 2 → ℝ)), A.Finite →
      let n := A.ncard
      n ≥ 10 →
      -- If there are at least c₀ * n² collinear pairs
      ((collinearPairs A).ncard : ℝ) ≥ c₀ * (n : ℝ)^2 →
      -- Then some 10 points lie on a cubic curve
      ∃ (B : Set (Fin 2 → ℝ)), B ⊆ A ∧ B.ncard = 10 ∧
        ∃ (C : Set (Fin 2 → ℝ)), IsCubicCurve C ∧ B ⊆ C := by
  sorry

/-- Through any 9 points in general position in ℝ², there passes a cubic curve.
    This is a classical fact from algebraic geometry. -/
theorem cubic_through_nine_points :
    ∀ (S : Set (Fin 2 → ℝ)), S.ncard ≤ 9 →
    ∃ (C : Set (Fin 2 → ℝ)), IsCubicCurve C ∧ S ⊆ C := by
  sorry

end Green69
