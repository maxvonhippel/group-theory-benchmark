/-
Problem 53. Suppose that F^n_2 is partitioned into sets A1, . . . , AK.
Does 2Ai contain a coset of codimension O_K(1) for some i?

Here 2Ai denotes the sumset Ai + Ai = {a + b : a, b ∈ Ai}.
A coset of codimension d is a translate of a subspace of dimension n - d.
O_K(1) means a constant that depends only on K, not on n.

The conjecture states: There exists a function f : ℕ → ℕ such that for all n, K,
if F_2^n is partitioned into K sets A_1, ..., A_K, then for some i,
the sumset 2A_i contains a coset of codimension at most f(K).
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Data.Set.Card
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Finset Pointwise

/-- The vector space F_2^n -/
abbrev F2n (n : ℕ) := Fin n → ZMod 2

/-- The sumset A + A (also written 2A in additive notation) -/
def sumset {α : Type*} [DecidableEq α] [Add α] (A : Finset α) : Finset α :=
  (A ×ˢ A).image fun p => p.1 + p.2

/-- A partition of a finite type into K nonempty parts -/
structure Partition (α : Type*) [Fintype α] [DecidableEq α] (K : ℕ) where
  /-- The K parts of the partition -/
  parts : Fin K → Finset α
  /-- The parts cover everything -/
  cover : ∀ x : α, ∃ i, x ∈ parts i
  /-- The parts are pairwise disjoint -/
  disjoint : ∀ i j, i ≠ j → Disjoint (parts i) (parts j)

/-- A coset of a submodule: v + W for some vector v and submodule W -/
def isCoset {n : ℕ} (S : Set (F2n n)) (W : Submodule (ZMod 2) (F2n n)) : Prop :=
  ∃ v : F2n n, S = v +ᵥ (W : Set (F2n n))

/-- The codimension of a submodule W of F_2^n is n - dim(W) -/
noncomputable def codimension {n : ℕ} (W : Submodule (ZMod 2) (F2n n)) : ℕ :=
  n - Module.finrank (ZMod 2) W

/-- A set S contains a coset of codimension at most d if there exists a submodule W
    with codimension at most d and a coset of W contained in S -/
def containsCosetOfCodimAtMost {n : ℕ} (S : Set (F2n n)) (d : ℕ) : Prop :=
  ∃ W : Submodule (ZMod 2) (F2n n),
    codimension W ≤ d ∧
    ∃ v : F2n n, ∀ w ∈ W, v + w ∈ S

/--
Problem 53 Conjecture:
There exists a function f : ℕ → ℕ such that for all n ≥ 1 and K ≥ 1,
if F_2^n is partitioned into K parts A_1, ..., A_K, then for some i,
the sumset 2A_i contains a coset of codimension at most f(K).

This is stated as: the sumset of some part contains a coset whose codimension
depends only on K (the number of parts), not on n (the dimension).
-/
theorem green_problem_53 :
    ∃ f : ℕ → ℕ,
      ∀ (n K : ℕ),
        n ≥ 1 → K ≥ 1 →
        ∀ (P : Partition (F2n n) K),
          ∃ i : Fin K,
            containsCosetOfCodimAtMost (sumset (P.parts i) : Set (F2n n)) (f K) := by
  sorry

/-- Alternative formulation: for each fixed K, there is a constant c_K such that
    for all n and all partitions of F_2^n into K parts, some 2A_i contains
    a coset of codimension at most c_K. -/
theorem green_problem_53_alt :
    ∀ K : ℕ, K ≥ 1 →
      ∃ c : ℕ,
        ∀ (n : ℕ),
          n ≥ 1 →
          ∀ (P : Partition (F2n n) K),
            ∃ i : Fin K,
              containsCosetOfCodimAtMost (sumset (P.parts i) : Set (F2n n)) c := by
  sorry

/-- Stronger conjecture mentioned in the problem:
    The bound could be O(log K), which would imply polynomial Bogolyubov-Freiman-Ruzsa -/
theorem green_problem_53_strong :
    ∃ C : ℝ, C > (0 : ℝ) ∧
      ∀ (n K : ℕ),
        n ≥ 1 → K ≥ 2 →
        ∀ (P : Partition (F2n n) K),
          ∃ i : Fin K,
            containsCosetOfCodimAtMost (sumset (P.parts i) : Set (F2n n))
              (Nat.ceil (C * Real.log K)) := by
  sorry
