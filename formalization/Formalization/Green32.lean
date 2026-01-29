/-
Problem 32. Let p be a prime and let A ⊂ Z/pZ be a set of size √p.
Is there a dilate of A with a gap of length 100√p?

Formalization:
- We work in Z/pZ where p is prime.
- A "dilate" of A by d ∈ (Z/pZ)ˣ is the set {d * a : a ∈ A}.
- A "gap" in a subset S of Z/pZ is a maximal sequence of consecutive elements
  (using the natural representatives 0, 1, ..., p-1) not in S.
- We interpret "size √p" as |A| = Nat.sqrt p.
- The problem asks: for all such A, does there exist a dilate with a gap of
  length at least 100 * √p?
-/

import Mathlib

namespace Green32

open Finset

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

/-- A gap starting at position `start` of length `len` in a subset S of Z/pZ
    means the elements start, start+1, ..., start+(len-1) are all not in S. -/
def hasGapAt (S : Finset (ZMod p)) (start : ZMod p) (len : ℕ) : Prop :=
  ∀ i : ℕ, i < len → (start + i : ZMod p) ∉ S

/-- A subset S of Z/pZ has a gap of length at least `len` if there exists
    some starting position where `len` consecutive elements are not in S. -/
def hasGapOfLength (S : Finset (ZMod p)) (len : ℕ) : Prop :=
  ∃ start : ZMod p, hasGapAt S start len

/-- The dilate of a set A by a unit d in Z/pZ is {d * a : a ∈ A}. -/
def dilate (d : (ZMod p)ˣ) (A : Finset (ZMod p)) : Finset (ZMod p) :=
  A.map ⟨fun a => d.val * a, fun _ _ h => by
    have hd : IsUnit (d : ZMod p) := d.isUnit
    exact (mul_right_injective₀ hd.ne_zero).eq_iff.mp h⟩

/--
**Green Problem 32:**

Let p be a prime and let A ⊂ Z/pZ be a set of size √p.
Is there a dilate of A with a gap of length 100√p?

This theorem states the conjectured positive answer: for any prime p and any
subset A of Z/pZ with |A| = ⌊√p⌋, there exists a nonzero d such that the
dilate d·A has a gap of length at least 100·⌊√p⌋.

Note: The constant 100 is part of the problem statement and represents
a large constant (the actual best constant is an open question).
-/
theorem green_problem_32 (A : Finset (ZMod p)) (hA : A.card = Nat.sqrt p) :
    ∃ d : (ZMod p)ˣ, hasGapOfLength (dilate d A) (100 * Nat.sqrt p) := by
  sorry

end Green32
