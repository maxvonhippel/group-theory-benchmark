import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Card

/-!
# Kourovka Problem 2.78

An IĒn-system of a finite group G is a set of all subgroups of some fixed order n
such that at least one of these subgroups is non-normal.

Various properties of positive integers are defined based on the groups having
exactly k IĒn-systems.
-/

variable {G : Type*} [Group G]

/-- A subgroup H of G is non-normal if it is not a normal subgroup -/
def IsNonNormal [Group G] (H : Subgroup G) : Prop :=
  ¬ H.Normal

/-- The set of all subgroups of G with a given cardinality n -/
def subgroupsOfOrder (G : Type*) [Group G] [Fintype G] (n : ℕ) : Set (Subgroup G) :=
  {H : Subgroup G | Nat.card H = n}

/-- A set of subgroups forms an IĒn-system if it consists of all subgroups of
some fixed order and contains at least one non-normal subgroup -/
def IsIEnSystem [Fintype G] (S : Set (Subgroup G)) : Prop :=
  ∃ n : ℕ, S = subgroupsOfOrder G n ∧ S.Nonempty ∧ ∃ H ∈ S, IsNonNormal H

/-- The set of all IĒn-systems of a finite group G -/
def IEnSystems (G : Type*) [Group G] [Fintype G] : Set (Set (Subgroup G)) :=
  {S | IsIEnSystem S}

/-- The number of IĒn-systems of a finite group G -/
noncomputable def numIEnSystems (G : Type*) [Group G] [Fintype G] : ℕ :=
  Set.ncard (IEnSystems G)

/-- A positive integer k is a soluble group-theoretic number if every finite group
having exactly k IĒn-systems is soluble -/
def IsSolubleGroupTheoreticNumber (k : ℕ) : Prop :=
  k > 0 ∧ ∀ (G : Type) [Group G] [Fintype G], numIEnSystems G = k → IsSolvable G

/-- A positive integer k is a non-soluble group-theoretic number if there exists
at least one non-soluble finite group having k IĒn-systems -/
def IsNonSolubleGroupTheoreticNumber (k : ℕ) : Prop :=
  k > 0 ∧ ∃ (G : Type) (_ : Group G) (_ : Fintype G), numIEnSystems G = k ∧ ¬ IsSolvable G

/-- A positive integer k is a simple group-theoretic number if there exists
at least one simple finite group having k IĒn-systems -/
def IsSimpleGroupTheoreticNumber (k : ℕ) : Prop :=
  k > 0 ∧ ∃ (G : Type) (_ : Group G) (_ : Fintype G), numIEnSystems G = k ∧ IsSimpleGroup G

/-- A positive integer k is a composite group-theoretic number if there are no
simple finite groups having k IĒn-systems -/
def IsCompositeGroupTheoreticNumber (k : ℕ) : Prop :=
  k > 0 ∧ ∀ (G : Type) [Group G] [Fintype G], numIEnSystems G = k → ¬ IsSimpleGroup G

/-- A positive integer k is an absolutely simple group-theoretic number if there
exists at least one simple finite group having k IĒn-systems and there are no
non-soluble non-simple finite groups having k IĒn-systems -/
def IsAbsolutelySimpleGroupTheoreticNumber (k : ℕ) : Prop :=
  k > 0 ∧
  (∃ (G : Type) (_ : Group G) (_ : Fintype G), numIEnSystems G = k ∧ IsSimpleGroup G) ∧
  (∀ (G : Type) [Group G] [Fintype G],
    numIEnSystems G = k → ¬ IsSolvable G → IsSimpleGroup G)

/-- The set of all soluble group-theoretic numbers -/
def solubleGroupTheoreticNumbers : Set ℕ :=
  {k | IsSolubleGroupTheoreticNumber k}

/-- The set of all absolutely simple group-theoretic numbers -/
def absolutelySimpleGroupTheoreticNumbers : Set ℕ :=
  {k | IsAbsolutelySimpleGroupTheoreticNumber k}

/-- Question 1a: Is the set of all soluble group-theoretic numbers finite? -/
theorem kourovka_2_78_soluble_finite_or_infinite :
    solubleGroupTheoreticNumbers.Finite ∨ solubleGroupTheoreticNumbers.Infinite := by
  sorry

/-- Question 1b: Is the set of all absolutely simple group-theoretic numbers finite? -/
theorem kourovka_2_78_absolutely_simple_finite_or_infinite :
    absolutelySimpleGroupTheoreticNumbers.Finite ∨
    absolutelySimpleGroupTheoreticNumbers.Infinite := by
  sorry

/-- Question 2: Do there exist composite but not soluble group-theoretic numbers?
That is, does there exist k such that no simple group has k IĒn-systems,
but some non-soluble group has k IĒn-systems? -/
theorem kourovka_2_78_composite_not_soluble_exists :
    (∃ k : ℕ, IsCompositeGroupTheoreticNumber k ∧ IsNonSolubleGroupTheoreticNumber k) ∨
    (∀ k : ℕ, IsCompositeGroupTheoreticNumber k → IsSolubleGroupTheoreticNumber k) := by
  sorry
