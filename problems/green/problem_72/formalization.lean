/-
Problem 72. What is the largest subset of the grid [N]² with no three points in a line?
In particular, for N sufficiently large is it impossible to have a set of size 2N with this property?

This formalizes the specific conjecture: For N sufficiently large, there is no subset of [N]²
of size 2N with no three points collinear.
-/

import Mathlib

/-- The grid [N]² = {1, ..., N} × {1, ..., N} represented as pairs of positive integers ≤ N -/
def Grid (N : ℕ) : Set (ℤ × ℤ) :=
  {p | 1 ≤ p.1 ∧ p.1 ≤ N ∧ 1 ≤ p.2 ∧ p.2 ≤ N}

/-- Three integer points are collinear if the signed area of the triangle they form is zero.
    For points (x₁, y₁), (x₂, y₂), (x₃, y₃), this is:
    x₁(y₂ - y₃) + x₂(y₃ - y₁) + x₃(y₁ - y₂) = 0 -/
def AreCollinear (p₁ p₂ p₃ : ℤ × ℤ) : Prop :=
  p₁.1 * (p₂.2 - p₃.2) + p₂.1 * (p₃.2 - p₁.2) + p₃.1 * (p₁.2 - p₂.2) = 0

/-- A set of points has no three collinear if for any three distinct points,
    they are not collinear -/
def NoThreeCollinear (S : Set (ℤ × ℤ)) : Prop :=
  ∀ p₁ p₂ p₃, p₁ ∈ S → p₂ ∈ S → p₃ ∈ S →
    p₁ ≠ p₂ → p₂ ≠ p₃ → p₁ ≠ p₃ → ¬AreCollinear p₁ p₂ p₃

/-- The main conjecture: For N sufficiently large, there is no subset of [N]²
    of size 2N with no three points collinear -/
theorem green_problem_72 :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ S : Finset (ℤ × ℤ),
      (↑S : Set (ℤ × ℤ)) ⊆ Grid N →
      NoThreeCollinear (↑S : Set (ℤ × ℤ)) →
      S.card < 2 * N := by
  sorry
