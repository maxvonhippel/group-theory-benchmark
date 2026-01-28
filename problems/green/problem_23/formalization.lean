/-
Problem 23. (Solved) Suppose that N is finitely coloured. Are there x, y of the
same colour such that x^2 + y^2 is a square?

Comments. This is a weaker version of the famous question asking whether
x^2 + y^2 = z^2 is partition-regular. (In that problem, z must also be the same colour.)

Update 2023. This problem has now been resolved by Frantzikinakis, Klurman and
Moreira [120]. The question of whether x^2 + y^2 = z^2 is partition regular
remains wide open.

We formalize the solved problem: For any finite coloring of ℕ⁺, there exist
x, y of the same color such that x² + y² is a perfect square.
-/

import Mathlib

namespace Green23

/-- Green Problem 23 (solved): For any finite coloring of the positive natural numbers,
    there exist positive x, y of the same color such that x² + y² is a perfect square.

    This was proved by Frantzikinakis, Klurman and Moreira (2023). -/
theorem green_problem_23 (k : ℕ) (hk : k ≥ 1) (color : ℕ+ → Fin k) :
    ∃ x y : ℕ+, color x = color y ∧ IsSquare (x.val ^ 2 + y.val ^ 2) := by
  sorry

/-- The stronger conjecture (still open): x² + y² = z² is partition regular.
    That is, for any finite coloring of ℕ⁺, there exist monochromatic x, y, z
    forming a Pythagorean triple. -/
theorem pythagorean_partition_regular_conjecture (k : ℕ) (hk : k ≥ 1) (color : ℕ+ → Fin k) :
    ∃ x y z : ℕ+, color x = color y ∧ color y = color z ∧ x.val ^ 2 + y.val ^ 2 = z.val ^ 2 := by
  sorry

end Green23
