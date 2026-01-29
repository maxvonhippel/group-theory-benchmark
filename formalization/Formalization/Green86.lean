/-
Problem 86. Let c > 0. Let A be a set of n (distinct) integers. Does there exist
θ such that no interval of length 1/n in ℝ/ℤ contains more than n^c of the numbers
θa (mod 1), a ∈ A?

The conjecture states that for any c > 0 and any finite set A of n distinct integers,
there exists θ ∈ ℝ such that the fractional parts {θa : a ∈ A} are well-distributed
in the sense that no interval of length 1/n contains more than n^c of them.

This is known for c > 1/3; see reference [187] in Green's book.
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Set Finset Real

noncomputable section

/-- The fractional part of a real number (value in [0, 1)) -/
def fracPart (x : ℝ) : ℝ := x - ⌊x⌋

/-- An interval in ℝ/ℤ of length ℓ starting at point t, represented as [t, t + ℓ) mod 1.
    We check membership by considering the fractional part. -/
def inCircleInterval (t ℓ x : ℝ) : Prop :=
  let t' := fracPart t
  let x' := fracPart x
  if t' + ℓ ≤ 1 then
    t' ≤ x' ∧ x' < t' + ℓ
  else
    -- Interval wraps around: [t', 1) ∪ [0, t' + ℓ - 1)
    t' ≤ x' ∨ x' < t' + ℓ - 1

instance : DecidablePred (inCircleInterval t ℓ) := fun x => by
  unfold inCircleInterval
  exact inferInstance

/-- Count of elements a in A such that fracPart(θ * a) lies in the interval [t, t + ℓ) mod 1 -/
def countInInterval (A : Finset ℤ) (θ t ℓ : ℝ) : ℕ :=
  (A.filter (fun a : ℤ => inCircleInterval t ℓ (θ * (a : ℝ)))).card

/--
**Green's Conjecture (Problem 86):**

For any c > 0 and any finite set A of n distinct integers (where n = |A|),
there exists θ ∈ ℝ such that for every interval of length 1/n in ℝ/ℤ,
the number of a ∈ A with fracPart(θ * a) in that interval is at most n^c.

Note: The problem asks whether this is true. The conjecture asserts that it is.
This is known for c > 1/3.
-/
theorem green_problem_86 :
    ∀ (c : ℝ), c > 0 →
    ∀ (A : Finset ℤ), A.card ≥ 1 →
    ∃ (θ : ℝ), ∀ (t : ℝ),
      (countInInterval A θ t (1 / A.card) : ℝ) ≤ (A.card : ℝ) ^ c := by
  sorry

end
