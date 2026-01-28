/-
Problem 76. Let A be a set of n points in the plane. Can one select a set A′ of n/2 points,
with the property that any axis-parallel rectangle containing 1000 points of A contains
at least one point of A′?

This is a question about weak ε-nets for axis-parallel rectangles.
A weak ε-net for a point set A with respect to a range space is a set A′ (not necessarily
a subset of A) such that every range containing at least ε|A| points of A also contains
at least one point of A′.

Here ε = 1000/n and the range space is axis-parallel rectangles.
The question asks if such a net of size n/2 always exists.

Comments mention:
- The answer is 'yes' if 1000 is replaced by C log log n (Alon, Kaplan, Nivasch, Sharir, Smorodinsky).
- If A′ is required to be a subset of A, the answer is 'no' (Noga Alon).
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Basic

open Set

/-- A point in the plane ℝ² -/
abbrev Point := EuclideanSpace ℝ (Fin 2)

/-- An axis-parallel rectangle in ℝ², defined by intervals [x₁, x₂] × [y₁, y₂] -/
structure AxisParallelRectangle where
  x₁ : ℝ
  x₂ : ℝ
  y₁ : ℝ
  y₂ : ℝ
  hx : x₁ ≤ x₂
  hy : y₁ ≤ y₂

/-- A point is inside an axis-parallel rectangle -/
def AxisParallelRectangle.contains (R : AxisParallelRectangle) (p : Point) : Prop :=
  R.x₁ ≤ p 0 ∧ p 0 ≤ R.x₂ ∧ R.y₁ ≤ p 1 ∧ p 1 ≤ R.y₂

/-- The set of points from A contained in rectangle R -/
def PointsInRectangle (A : Set Point) (R : AxisParallelRectangle) : Set Point :=
  {p ∈ A | R.contains p}

/-- A finite set of n points -/
structure FinitePointSet (n : ℕ) where
  points : Set Point
  finite : points.Finite
  card_eq : points.ncard = n

/-- The weak ε-net property: A′ hits every rectangle containing at least k points of A -/
def IsWeakNet (A : Set Point) (A' : Set Point) (k : ℕ) : Prop :=
  ∀ R : AxisParallelRectangle, (PointsInRectangle A R).ncard ≥ k →
    ∃ p ∈ A', R.contains p

/--
Problem 76: Does there exist, for every set A of n points in the plane,
a set A′ of n/2 points such that every axis-parallel rectangle containing
at least 1000 points of A contains at least one point of A′?

This formulates the question as: Does there exist such a weak net for all finite point sets?
-/
def Green76 : Prop :=
  ∀ n : ℕ, n ≥ 2000 →
  ∀ A : FinitePointSet n,
  ∃ A' : Set Point,
    A'.Finite ∧
    A'.ncard = n / 2 ∧
    IsWeakNet A.points A' 1000

/--
The known positive result: The answer is yes if 1000 is replaced by C log log n
for some constant C.
-/
def Green76LogLogVersion : Prop :=
  ∃ C : ℕ, C > 0 ∧
  ∀ n : ℕ, n ≥ 2 →
  ∀ A : FinitePointSet n,
  ∃ A' : Set Point,
    A'.Finite ∧
    A'.ncard = n / 2 ∧
    IsWeakNet A.points A' (C * Nat.log 2 (Nat.log 2 n))

/--
The negative result when A′ must be a subset of A (strong ε-net):
There exist point sets where no subset of size n/2 is an ε-net for k = 1000.
-/
def Green76SubsetNegative : Prop :=
  ∃ n : ℕ, n ≥ 2000 ∧
  ∃ A : FinitePointSet n,
  ¬∃ A' : Set Point,
    A' ⊆ A.points ∧
    A'.ncard = n / 2 ∧
    IsWeakNet A.points A' 1000

/-- The main conjecture stated as a theorem to prove or disprove -/
theorem green76_conjecture : Green76 := by
  sorry

/-- The subset version is known to be false -/
theorem green76_subset_negative : Green76SubsetNegative := by
  sorry
