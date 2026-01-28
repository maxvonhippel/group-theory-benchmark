/-
Problem 75. Let X ⊂ R² be a set of n points. Does there exist a line ℓ through at
least two points of X such that the numbers of points on either side of ℓ differ
by at most 100?

Comments: This is known as the Kupitz-Perles conjecture. Pinchasi has shown it is
true with 100 replaced by O(log log n); Alon has shown it cannot be improved to 2.

We formalize:
1. The notion of a line through two distinct points
2. Points being strictly on one side or the other of a line
3. The main conjecture: for any finite point set, such a "balanced" line exists
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Finite.Basic

open Set Classical

noncomputable section

namespace Green75

/-- The 2D Euclidean plane -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- A line in R² defined by equation ax + by = c, with (a,b) ≠ 0 -/
structure Line where
  a : ℝ
  b : ℝ
  c : ℝ
  nonzero : a ≠ 0 ∨ b ≠ 0

/-- A point lies on a line -/
def Line.contains (L : Line) (p : Plane) : Prop :=
  L.a * p 0 + L.b * p 1 = L.c

/-- A point is strictly on the positive side of a line -/
def Line.positiveSide (L : Line) (p : Plane) : Prop :=
  L.a * p 0 + L.b * p 1 > L.c

/-- A point is strictly on the negative side of a line -/
def Line.negativeSide (L : Line) (p : Plane) : Prop :=
  L.a * p 0 + L.b * p 1 < L.c

/-- The line through two distinct points p and q -/
def lineThrough (p q : Plane) (hne : p ≠ q) : Line where
  -- Line through p and q: (q₁ - p₁)(x - p₀) - (q₀ - p₀)(y - p₁) = 0
  -- i.e., (q₁ - p₁)x - (q₀ - p₀)y = (q₁ - p₁)p₀ - (q₀ - p₀)p₁
  a := q 1 - p 1
  b := -(q 0 - p 0)
  c := (q 1 - p 1) * p 0 - (q 0 - p 0) * p 1
  nonzero := by
    by_contra h
    push_neg at h
    have ha : q 1 = p 1 := by linarith [h.1]
    have hb : q 0 = p 0 := by linarith [h.2]
    have : q = p := by
      ext i
      fin_cases i <;> simp_all
    exact hne this.symm

/-- A line passes through at least two points of a finite set -/
def passesThoughTwoPoints (L : Line) (X : Finset Plane) : Prop :=
  ∃ p q : Plane, p ∈ X ∧ q ∈ X ∧ p ≠ q ∧ L.contains p ∧ L.contains q

/-- The set of points strictly on the positive side of a line -/
def pointsOnPositiveSide (L : Line) (X : Finset Plane) : Set Plane :=
  { p ∈ X | L.positiveSide p }

/-- The set of points strictly on the negative side of a line -/
def pointsOnNegativeSide (L : Line) (X : Finset Plane) : Set Plane :=
  { p ∈ X | L.negativeSide p }

/-- Count of points strictly on the positive side of a line -/
def countPositiveSide (L : Line) (X : Finset Plane) : ℕ :=
  Nat.card (pointsOnPositiveSide L X)

/-- Count of points strictly on the negative side of a line -/
def countNegativeSide (L : Line) (X : Finset Plane) : ℕ :=
  Nat.card (pointsOnNegativeSide L X)

/-- The absolute difference between points on each side -/
def sideImbalance (L : Line) (X : Finset Plane) : ℕ :=
  Int.natAbs (countPositiveSide L X - countNegativeSide L X : ℤ)

/-- A line is k-balanced with respect to a point set if the numbers of
    points on either side differ by at most k -/
def isBalanced (L : Line) (X : Finset Plane) (k : ℕ) : Prop :=
  sideImbalance L X ≤ k

/--
Problem 75 (Kupitz-Perles Conjecture): For any finite set X of points in the plane,
there exists a line through at least two points of X such that the numbers of points
on either side of the line differ by at most 100.
-/
theorem green_problem_75 :
    ∀ (X : Finset Plane), X.card ≥ 2 →
      ∃ L : Line, passesThoughTwoPoints L X ∧ isBalanced L X 100 := by
  sorry

/--
Pinchasi's stronger result: The bound can be improved to O(log log n).
Here we state it as: there exists a constant C such that for all n ≥ 2 and
all X with |X| = n, there exists a line through two points with imbalance
at most C * log(log n) + C.
-/
theorem green_problem_75_pinchasi :
    ∃ C : ℕ, ∀ (X : Finset Plane), X.card ≥ 2 →
      ∃ L : Line, passesThoughTwoPoints L X ∧
        sideImbalance L X ≤ C * Nat.log 2 (Nat.log 2 X.card) + C := by
  sorry

/--
Alon's negative result: The bound cannot be improved to 2.
There exists a finite point configuration where every line through two points
has at least 3 more points on one side than the other.
-/
theorem green_problem_75_alon_counterexample :
    ∃ (X : Finset Plane), X.card ≥ 2 ∧
      ∀ L : Line, passesThoughTwoPoints L X → sideImbalance L X ≥ 3 := by
  sorry

end Green75
