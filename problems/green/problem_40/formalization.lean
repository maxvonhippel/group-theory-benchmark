/-
Problem 40: On the covering density function f(r) for linear covering codes

Let r be a fixed positive integer, and let H(r) be the Hamming ball of radius r in F₂ⁿ.
Let f(r) be the smallest constant such that there exists an infinite sequence of ns
together with subspaces Vₙ ≤ F₂ⁿ with Vₙ + H(r) = F₂ⁿ and
|Vₙ| = (f(r) + o(1)) · 2ⁿ / |H(r)|.

Question: Does f(r) → ∞?

This is an OPEN QUESTION, not a theorem. We formalize the relevant definitions
and state the question as a proposition (which may or may not be true).
-/

import Mathlib

open Finset BigOperators

namespace Green40

/-- The Hamming distance between two vectors in (ZMod 2)^n -/
def hammingDist {n : ℕ} (v w : Fin n → ZMod 2) : ℕ :=
  (Finset.univ.filter fun i => v i ≠ w i).card

/-- The Hamming ball of radius r centered at v in (ZMod 2)^n -/
def hammingBall {n : ℕ} (v : Fin n → ZMod 2) (r : ℕ) : Set (Fin n → ZMod 2) :=
  {w | hammingDist v w ≤ r}

/-- The Hamming ball of radius r centered at 0 in (ZMod 2)^n -/
def hammingBallAtZero (n : ℕ) (r : ℕ) : Set (Fin n → ZMod 2) :=
  hammingBall 0 r

/-- The size of the Hamming ball of radius r in (ZMod 2)^n.
    This equals ∑_{i=0}^{min(r,n)} C(n,i) -/
def hammingBallSize (n r : ℕ) : ℕ :=
  (Finset.range (min r n + 1)).sum fun i => n.choose i

/-- A subspace V of (ZMod 2)^n is a covering code of radius r if V + H(r) = (ZMod 2)^n,
    i.e., every vector is within Hamming distance r of some codeword. -/
def isCoveringCode {n : ℕ} (V : Submodule (ZMod 2) (Fin n → ZMod 2)) (r : ℕ) : Prop :=
  ∀ w : Fin n → ZMod 2, ∃ v ∈ V, hammingDist v w ≤ r

/-- The covering density of a subspace V with respect to radius r.
    This is |V| · |H(r)| / 2^n, measuring how efficiently V covers.
    We use the finrank to compute the "size" as 2^(finrank). -/
noncomputable def coveringDensity {n : ℕ} (V : Submodule (ZMod 2) (Fin n → ZMod 2)) (r : ℕ) : ℝ :=
  (2 : ℝ) ^ (Module.finrank (ZMod 2) V) * (hammingBallSize n r : ℝ) / (2 ^ n : ℝ)

/-- A sequence of covering codes is a function assigning to each n (or selected ns)
    a subspace that covers (ZMod 2)^n with radius r. -/
structure CoveringCodeSequence (r : ℕ) where
  /-- The sequence of dimensions (strictly increasing) -/
  dims : ℕ → ℕ
  dims_strictMono : StrictMono dims
  /-- For each index i, the subspace in (ZMod 2)^(dims i) -/
  codes : (i : ℕ) → Submodule (ZMod 2) (Fin (dims i) → ZMod 2)
  /-- Each code is a covering code of radius r -/
  is_covering : ∀ i, isCoveringCode (codes i) r

/-- The asymptotic covering density of a sequence of covering codes.
    This is the lim sup of the covering densities as the dimension grows. -/
noncomputable def asymptoticDensity {r : ℕ} (seq : CoveringCodeSequence r) : ℝ :=
  Filter.limsup (fun i => coveringDensity (seq.codes i) r) Filter.atTop

/-- f(r) is the infimum of asymptotic densities over all covering code sequences.
    Note: This is the infimum over all possible infinite sequences of covering codes. -/
noncomputable def f (r : ℕ) : ℝ :=
  sInf {d : ℝ | ∃ seq : CoveringCodeSequence r, asymptoticDensity seq = d}

/-
The main open question: Does f(r) → ∞ as r → ∞?

We formalize this as a proposition. Note that this is an OPEN PROBLEM, so we do not
claim to know whether this is true or false.
-/

/-- The open question: Does f(r) tend to infinity as r tends to infinity? -/
def greenProblem40 : Prop :=
  Filter.Tendsto (fun r => f r) Filter.atTop Filter.atTop

/-
Known result: f(1) = 1, which follows from the existence of Hamming codes.
The Hamming code for parameters m uses n = 2^m - 1 and achieves perfect covering.
-/

/-- Hamming codes achieve f(1) = 1 (stated but not proved) -/
theorem f_one_eq_one : f 1 = 1 := by
  sorry

end Green40
