/-
Problem 85: Carbery's Rectangle Problem

Suppose that A is an open subset of [0, 1]² with measure α. Are there four points in A
determining an axis-parallel rectangle with area ⩾ cα²?

This is often known as 'Carbery's rectangle problem' from a joint paper of Carbery, Christ
and Wright.
-/

import Mathlib

open MeasureTheory Set

namespace Green85

/-- The unit square [0,1]². -/
def unitSquare : Set (ℝ × ℝ) := Icc 0 1 ×ˢ Icc 0 1

/-- Four points form an axis-parallel rectangle with the specified corners. -/
def FormsAxisParallelRectangle (p₁ p₂ p₃ p₄ : ℝ × ℝ) (x₁ x₂ y₁ y₂ : ℝ) : Prop :=
  x₁ < x₂ ∧ y₁ < y₂ ∧
  ({p₁, p₂, p₃, p₄} : Set (ℝ × ℝ)) = {(x₁, y₁), (x₁, y₂), (x₂, y₁), (x₂, y₂)}

/-- Four points determine some axis-parallel rectangle. -/
def DeterminesAxisParallelRectangle (p₁ p₂ p₃ p₄ : ℝ × ℝ) : Prop :=
  ∃ x₁ x₂ y₁ y₂ : ℝ, FormsAxisParallelRectangle p₁ p₂ p₃ p₄ x₁ x₂ y₁ y₂

/-- The area of an axis-parallel rectangle with given corner coordinates. -/
def rectangleAreaFromCorners (x₁ x₂ y₁ y₂ : ℝ) : ℝ := (x₂ - x₁) * (y₂ - y₁)

/-- Carbery's Rectangle Problem: There exists a constant c > 0 such that for any
    open subset A of [0,1]² with Lebesgue measure α > 0, there exist four points in A
    forming an axis-parallel rectangle with area at least c * α².

    Note: We require α > 0 since otherwise the statement would be vacuously false
    (no points to choose from) or trivially satisfied (area bound is 0). -/
theorem carberys_rectangle_problem :
    ∃ c : ℝ, c > 0 ∧ ∀ A : Set (ℝ × ℝ),
      IsOpen A → A ⊆ unitSquare →
      ∀ α : ℝ, α > 0 → (volume A).toReal = α →
      ∃ p₁ p₂ p₃ p₄ : ℝ × ℝ,
        p₁ ∈ A ∧ p₂ ∈ A ∧ p₃ ∈ A ∧ p₄ ∈ A ∧
        ∃ x₁ x₂ y₁ y₂ : ℝ,
          FormsAxisParallelRectangle p₁ p₂ p₃ p₄ x₁ x₂ y₁ y₂ ∧
          rectangleAreaFromCorners x₁ x₂ y₁ y₂ ≥ c * α ^ 2 := by
  sorry

/-- Known partial result: Using Cauchy-Schwarz, one can show that there must exist
    a rectangle with area ≫ α²(log 1/α)⁻¹. This is stated (not proved) here. -/
theorem cauchy_schwarz_bound :
    ∃ c : ℝ, c > 0 ∧ ∀ A : Set (ℝ × ℝ),
      IsOpen A → A ⊆ unitSquare →
      ∀ α : ℝ, 0 < α → α < 1 → (volume A).toReal = α →
      ∃ p₁ p₂ p₃ p₄ : ℝ × ℝ,
        p₁ ∈ A ∧ p₂ ∈ A ∧ p₃ ∈ A ∧ p₄ ∈ A ∧
        ∃ x₁ x₂ y₁ y₂ : ℝ,
          FormsAxisParallelRectangle p₁ p₂ p₃ p₄ x₁ x₂ y₁ y₂ ∧
          rectangleAreaFromCorners x₁ x₂ y₁ y₂ ≥ c * α ^ 2 / Real.log (1 / α) := by
  sorry

end Green85
