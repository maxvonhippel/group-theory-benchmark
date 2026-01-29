/-
Problem 57. Let G be an abelian group, and consider the space Φ(G) of all functions on G
which are convex combinations of functions of the form

ϕ(g) := E_{x₁+x₂+x₃=g} f₁(x₂, x₃) f₂(x₁, x₃) f₃(x₁, x₂)

with ‖fᵢ‖∞ ≤ 1. Let Φ′(G) be the space of functions defined similarly, but with f₃(x₁, x₂)
now required to be a function of x₁ + x₂. Do Φ(G) and Φ′(G) coincide?

This is formalized for finite abelian groups where the expectation becomes a normalized sum.
-/
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Fintype.Basic

open Finset BigOperators

variable (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- The set of triples (x₁, x₂, x₃) in G³ such that x₁ + x₂ + x₃ = g -/
def Green57.triplesSummingTo (g : G) : Finset (G × G × G) :=
  Finset.univ.filter (fun t => t.1 + t.2.1 + t.2.2 = g)

/-- A function f : G × G → ℂ is bounded by 1 in sup norm -/
def Green57.BoundedByOne (f : G × G → ℂ) : Prop :=
  ∀ p : G × G, ‖f p‖ ≤ 1

/-- The basic building block function ϕ for the space Φ(G).
    ϕ(g) = (1/|G|²) ∑_{x₁+x₂+x₃=g} f₁(x₂, x₃) * f₂(x₁, x₃) * f₃(x₁, x₂)
    where the sum ranges over all triples summing to g. -/
noncomputable def Green57.phiFunction
    (f₁ f₂ f₃ : G × G → ℂ) : G → ℂ := fun g =>
  (Fintype.card G : ℂ)⁻¹ ^ 2 *
    ∑ t ∈ Green57.triplesSummingTo G g,
      f₁ (t.2.1, t.2.2) * f₂ (t.1, t.2.2) * f₃ (t.1, t.2.1)

/-- A function is in the generating set for Φ(G) if it arises from bounded functions f₁, f₂, f₃ -/
def Green57.InPhiGenerators (φ : G → ℂ) : Prop :=
  ∃ (f₁ f₂ f₃ : G × G → ℂ),
    Green57.BoundedByOne G f₁ ∧ Green57.BoundedByOne G f₂ ∧ Green57.BoundedByOne G f₃ ∧
    φ = Green57.phiFunction G f₁ f₂ f₃

/-- A function f₃ : G × G → ℂ factors through the sum, i.e., f₃(x₁, x₂) depends only on x₁ + x₂ -/
def Green57.FactorsThroughSum (f₃ : G × G → ℂ) : Prop :=
  ∃ h : G → ℂ, ∀ x₁ x₂ : G, f₃ (x₁, x₂) = h (x₁ + x₂)

/-- A function is in the generating set for Φ'(G) if it arises from bounded functions f₁, f₂, f₃
    where f₃ factors through the sum -/
def Green57.InPhiPrimeGenerators (φ : G → ℂ) : Prop :=
  ∃ (f₁ f₂ f₃ : G × G → ℂ),
    Green57.BoundedByOne G f₁ ∧ Green57.BoundedByOne G f₂ ∧ Green57.BoundedByOne G f₃ ∧
    Green57.FactorsThroughSum G f₃ ∧
    φ = Green57.phiFunction G f₁ f₂ f₃

/-- A convex combination coefficient structure: non-negative reals summing to 1 -/
structure Green57.ConvexCoeffs (ι : Type*) [Fintype ι] where
  coeffs : ι → ℝ
  nonneg : ∀ i, 0 ≤ coeffs i
  sum_one : ∑ i, coeffs i = 1

/-- The space Φ(G): convex combinations of generator functions -/
def Green57.InPhi (φ : G → ℂ) : Prop :=
  ∃ (n : ℕ) (_ : n > 0) (generators : Fin n → G → ℂ) (c : Green57.ConvexCoeffs (Fin n)),
    (∀ i, Green57.InPhiGenerators G (generators i)) ∧
    φ = fun g => ∑ i, (c.coeffs i : ℂ) * generators i g

/-- The space Φ'(G): convex combinations of generator functions with restricted f₃ -/
def Green57.InPhiPrime (φ : G → ℂ) : Prop :=
  ∃ (n : ℕ) (_ : n > 0) (generators : Fin n → G → ℂ) (c : Green57.ConvexCoeffs (Fin n)),
    (∀ i, Green57.InPhiPrimeGenerators G (generators i)) ∧
    φ = fun g => ∑ i, (c.coeffs i : ℂ) * generators i g

/-- Main theorem: Φ'(G) ⊆ Φ(G) is obvious since Φ' has more restrictions -/
theorem Green57.PhiPrime_subset_Phi : ∀ φ : G → ℂ, Green57.InPhiPrime G φ → Green57.InPhi G φ := by
  intro φ ⟨n, hn, generators, c, hgens, hφ⟩
  refine ⟨n, hn, generators, c, ?_, hφ⟩
  intro i
  obtain ⟨f₁, f₂, f₃, hf₁, hf₂, hf₃, _, heq⟩ := hgens i
  exact ⟨f₁, f₂, f₃, hf₁, hf₂, hf₃, heq⟩

/--
Problem 57: Do Φ(G) and Φ'(G) coincide?

This asks whether every function in Φ(G) is also in Φ'(G).
The conjecture is that this is FALSE - there exist functions in Φ(G) \ Φ'(G).
-/
theorem Green57.problem_57 : (∀ φ : G → ℂ, Green57.InPhi G φ → Green57.InPhiPrime G φ) ↔
    (∀ φ : G → ℂ, Green57.InPhi G φ ↔ Green57.InPhiPrime G φ) := by
  constructor
  · intro h φ
    exact ⟨h φ, Green57.PhiPrime_subset_Phi G φ⟩
  · intro h φ hφ
    exact (h φ).mp hφ

/-- The open problem: Is every function in Φ(G) also in Φ'(G)?
    Expected answer: No (i.e., this statement is false for some G) -/
theorem Green57.problem_57_main_question : ∀ φ : G → ℂ, Green57.InPhi G φ → Green57.InPhiPrime G φ := by
  sorry
