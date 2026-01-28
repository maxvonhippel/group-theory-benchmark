/-
Problem 24. If A is a set of n integers, what is the maximum number of affine
translates of the set {0, 1, 3} that can A contain?

Comments. This problem was apparently raised by Ganguly. I heard it from Robin
Pemantle. It seems likely that the answer is (1/3 + o(1))n^2, but this is not known.
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.Basic
import Mathlib.Order.SupIndep

open Finset

/-- An affine translate of {0, 1, 3} by a is the set {a, a+1, a+3} -/
def translateOf013 (a : ℤ) : Finset ℤ := {a, a + 1, a + 3}

/-- A translate of {0, 1, 3} is contained in A if all three elements are in A -/
def containsTranslate (A : Finset ℤ) (a : ℤ) : Prop :=
  translateOf013 a ⊆ A

/-- The number of translates of {0, 1, 3} contained in A -/
noncomputable def countTranslates (A : Finset ℤ) : ℕ :=
  (A.filter (fun a => translateOf013 a ⊆ A)).card

/-- Problem 24: Characterize the maximum number of translates of {0, 1, 3}
    that can be contained in a set of n integers.

    The conjecture mentioned in the problem is that the answer is (1/3 + o(1)) * n^2,
    but this is stated to be unknown.

    We state this as: there exists some function f : ℕ → ℕ giving the maximum. -/
theorem green_problem_24 :
    ∃ f : ℕ → ℕ, ∀ n : ℕ, ∀ A : Finset ℤ, A.card = n → countTranslates A ≤ f n := by
  sorry

/-- The conjectured lower bound: there exist sets achieving roughly n²/3 translates -/
theorem green_problem_24_conjectured_lower_bound :
    ∀ n : ℕ, n > 0 → ∃ A : Finset ℤ, A.card = n ∧
      countTranslates A ≥ n * (n - 1) / 6 := by
  sorry
