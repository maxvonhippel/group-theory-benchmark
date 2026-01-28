/-
Kourovka Notebook Problem 2.78 (P. I. Trofimov)

Definitions:
- An "IĒn-system" of a finite group G is a set of all subgroups of the same given order
  that contains at least one non-normal subgroup.
- Various types of "group-theoretic numbers" are defined based on properties of finite
  groups having exactly k IĒn-systems.

Questions asked:
1. Are the sets of all soluble and of all absolutely simple group-theoretic numbers
   finite or infinite?
2. Do there exist composite, but not soluble group-theoretic numbers?

NOTE: This problem asks open research questions rather than stating theorems. We formalize
the definitions and state the questions as separate conjectures (which would need their
truth values determined to be proven).
-/

import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Set.Finite.Basic
import Mathlib.SetTheory.Cardinal.Finite

universe u

variable {G : Type u} [Group G]

/--
A subgroup H of G is non-normal if it is not a normal subgroup.
-/
def Subgroup.IsNonNormal (H : Subgroup G) : Prop :=
  ¬(H.Normal)

/--
The set of all subgroups of G with a given cardinality n.
-/
def subgroupsOfOrder (G : Type u) [Group G] [Fintype G] (n : ℕ) : Set (Subgroup G) :=
  {H : Subgroup G | ∃ (hfin : Fintype H), @Fintype.card H hfin = n}

/--
A set of subgroups forms an IĒn-system if:
1. It consists of all subgroups of some fixed order n
2. It contains at least one non-normal subgroup

In other words, an IĒn-system is the set of all subgroups of order n for some n,
where at least one such subgroup is non-normal.
-/
def IsIEnSystem (G : Type u) [Group G] [Fintype G] (S : Set (Subgroup G)) : Prop :=
  ∃ n : ℕ, S = subgroupsOfOrder G n ∧ S.Nonempty ∧ ∃ H ∈ S, Subgroup.IsNonNormal H

/--
The set of all IĒn-systems of a finite group G.
-/
def allIEnSystems (G : Type u) [Group G] [Fintype G] : Set (Set (Subgroup G)) :=
  {S | IsIEnSystem G S}

/--
The number of IĒn-systems of a finite group G.
For a finite group, there are finitely many subgroups, hence finitely many possible orders,
hence finitely many IĒn-systems.
-/
noncomputable def numIEnSystems (G : Type u) [Group G] [Fintype G] [DecidableEq (Subgroup G)] : ℕ :=
  Nat.card (allIEnSystems G)

/--
A positive integer k is a "soluble group-theoretic number" if every finite group
having exactly k IĒn-systems is soluble.
(We fix universe level u for the groups in the definition.)
-/
def IsSolubleGroupTheoreticNumber (k : ℕ) : Prop :=
  k > 0 ∧ ∀ (G : Type u) [Group G] [Fintype G] [DecidableEq (Subgroup G)],
    numIEnSystems G = k → IsSolvable G

/--
A positive integer k is a "non-soluble group-theoretic number" if there exists
at least one non-soluble finite group having k IĒn-systems.
-/
def IsNonSolubleGroupTheoreticNumber (k : ℕ) : Prop :=
  k > 0 ∧ ∃ (G : Type u) (_ : Group G) (_ : Fintype G) (_ : DecidableEq (Subgroup G)),
    @numIEnSystems G _ _ _ = k ∧ ¬IsSolvable G

/--
A positive integer k is a "simple group-theoretic number" if there exists
at least one simple finite group having k IĒn-systems.
-/
def IsSimpleGroupTheoreticNumber (k : ℕ) : Prop :=
  k > 0 ∧ ∃ (G : Type u) (_ : Group G) (_ : Fintype G) (_ : DecidableEq (Subgroup G)),
    @numIEnSystems G _ _ _ = k ∧ IsSimpleGroup G

/--
A positive integer k is a "composite group-theoretic number" if there are no
simple finite groups having k IĒn-systems.
-/
def IsCompositeGroupTheoreticNumber (k : ℕ) : Prop :=
  k > 0 ∧ ∀ (G : Type u) [Group G] [Fintype G] [DecidableEq (Subgroup G)],
    numIEnSystems G = k → ¬IsSimpleGroup G

/--
A positive integer k is an "absolutely simple group-theoretic number" if:
1. There exists at least one simple finite group having k IĒn-systems, AND
2. There are no non-soluble non-simple finite groups having k IĒn-systems.
-/
def IsAbsolutelySimpleGroupTheoreticNumber (k : ℕ) : Prop :=
  k > 0 ∧
  (∃ (G : Type u) (_ : Group G) (_ : Fintype G) (_ : DecidableEq (Subgroup G)),
    @numIEnSystems G _ _ _ = k ∧ IsSimpleGroup G) ∧
  (∀ (G : Type u) [Group G] [Fintype G] [DecidableEq (Subgroup G)],
    numIEnSystems G = k → ¬IsSolvable G → IsSimpleGroup G)

/--
The set of all soluble group-theoretic numbers.
-/
def solubleGroupTheoreticNumbers : Set ℕ :=
  {k | IsSolubleGroupTheoreticNumber.{u} k}

/--
The set of all absolutely simple group-theoretic numbers.
-/
def absolutelySimpleGroupTheoreticNumbers : Set ℕ :=
  {k | IsAbsolutelySimpleGroupTheoreticNumber.{u} k}

/-!
## The Questions as Conjectures

The problem asks whether certain sets are finite or infinite, and whether certain
numbers exist. Since these are open questions, we state both possibilities as
separate (mutually exclusive) conjectures.
-/

/--
Question 1a: Is the set of all soluble group-theoretic numbers finite?
-/
theorem kourovka_2_78_soluble_finite :
    solubleGroupTheoreticNumbers.Finite := by
  sorry

/--
Alternative Question 1a: Is the set of all soluble group-theoretic numbers infinite?
-/
theorem kourovka_2_78_soluble_infinite :
    solubleGroupTheoreticNumbers.Infinite := by
  sorry

/--
Question 1b: Is the set of all absolutely simple group-theoretic numbers finite?
-/
theorem kourovka_2_78_absolutely_simple_finite :
    absolutelySimpleGroupTheoreticNumbers.Finite := by
  sorry

/--
Alternative Question 1b: Is the set of all absolutely simple group-theoretic numbers infinite?
-/
theorem kourovka_2_78_absolutely_simple_infinite :
    absolutelySimpleGroupTheoreticNumbers.Infinite := by
  sorry

/--
Question 2: Do there exist composite but not soluble group-theoretic numbers?

A number is composite but not soluble if:
- It is composite (no simple groups have this many IĒn-systems)
- It is not soluble (there exists a non-soluble group with this many IĒn-systems)
-/
theorem kourovka_2_78_composite_not_soluble_exists :
    ∃ k : ℕ, IsCompositeGroupTheoreticNumber k ∧ ¬IsSolubleGroupTheoreticNumber k := by
  sorry

/--
Alternative Question 2: There are no composite but not soluble group-theoretic numbers.
-/
theorem kourovka_2_78_composite_not_soluble_none :
    ∀ k : ℕ, IsCompositeGroupTheoreticNumber k → IsSolubleGroupTheoreticNumber k := by
  sorry
