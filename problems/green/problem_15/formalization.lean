import Mathlib

/-!
# Problem 15

Does there exist a Lipschitz function f : ℤ → ℤ whose graph
Γ = {(n, f(n)) : n ∈ ℤ} ⊂ ℤ² is free of 3-term arithmetic progressions?

Note: The original problem states f : N → Z but then uses n ∈ Z in the graph.
We interpret this as f : ℤ → ℤ for consistency.
-/

/-- A function f : ℤ → ℤ is Lipschitz if there exists a constant C such that
    |f(x) - f(y)| ≤ C * |x - y| for all x, y ∈ ℤ -/
def IsLipschitzInt (f : ℤ → ℤ) : Prop :=
  ∃ C : ℕ, ∀ x y : ℤ, |f x - f y| ≤ C * |x - y|

/-- Three points in ℤ² form an arithmetic progression if they are distinct and
    the middle point is the average of the other two (componentwise) -/
def IsArithmeticProgressionZ2 (p q r : ℤ × ℤ) : Prop :=
  p ≠ q ∧ q ≠ r ∧ p ≠ r ∧ 2 * q.1 = p.1 + r.1 ∧ 2 * q.2 = p.2 + r.2

/-- The graph of a function f : ℤ → ℤ -/
def graphZ (f : ℤ → ℤ) : Set (ℤ × ℤ) :=
  {p | ∃ n : ℤ, p = (n, f n)}

/-- A set is free of 3-term arithmetic progressions if no three distinct points
    in the set form an arithmetic progression -/
def APFree (S : Set (ℤ × ℤ)) : Prop :=
  ∀ p q r : ℤ × ℤ, p ∈ S → q ∈ S → r ∈ S → ¬IsArithmeticProgressionZ2 p q r

/-- Problem 15: Does there exist a Lipschitz function f : ℤ → ℤ whose graph
    is free of 3-term arithmetic progressions? -/
theorem problem_15 :
    ∃ f : ℤ → ℤ, IsLipschitzInt f ∧ APFree (graphZ f) := by
  sorry
