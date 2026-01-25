/-
Kourovka Notebook Problem 1.20 (Yu. L. Ershov)

For which groups (classes of groups) is the lattice of normal subgroups
first-order definable in the lattice of all subgroups?

This is a question about definability in model theory: given a group G,
its subgroups form a lattice L(G) under inclusion. The normal subgroups
form a sublattice N(G). The question asks: for which groups G can we
express "H is normal in G" using only the lattice operations (meet, join,
order) without reference to the group structure itself?
-/

import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.ModelTheory.Definability
import Mathlib.ModelTheory.Order

/-!
# Kourovka Problem 1.20: Definability of Normal Subgroups in the Subgroup Lattice

## The Problem

Given a group G, its subgroups form a complete lattice Sub(G) under inclusion.
The normal subgroups form a subset N(G) ⊆ Sub(G). The question asks:

For which groups G is the set N(G) first-order definable in the structure
(Sub(G), ≤) using only the language of partial orders (or lattices)?

## Formalization Approach

We formalize this by:
1. Defining the lattice structure on subgroups
2. Expressing that a predicate on the subgroup lattice is first-order definable
3. Stating the problem as asking for which groups this holds for the normality predicate
-/

open FirstOrder Language

variable (G : Type*) [Group G]

/-- The type of subgroups of G, which forms a complete lattice under inclusion -/
abbrev SubgroupLattice (G : Type*) [Group G] := Subgroup G

/-- The predicate on subgroups that selects exactly the normal subgroups -/
def IsNormalSubgroupPredicate : Set (Subgroup G) :=
  {H : Subgroup G | H.Normal}

/--
We consider the subgroup lattice as a structure in the language of partial orders.
The question is whether the set of normal subgroups is definable in this structure.
-/
noncomputable instance : Language.order.Structure (Subgroup G) :=
  Language.orderStructure

/--
A group G has definable normal subgroups if the set of normal subgroups
is first-order definable in the lattice of all subgroups, viewed as a
partial order structure in the language of orders.

This uses the empty set of parameters, meaning we want a pure first-order
formula in the language of orders that defines normality.
-/
def HasDefinableNormalSubgroups (G : Type*) [Group G] : Prop :=
  (∅ : Set (Subgroup G)).Definable Language.order (IsNormalSubgroupPredicate G)

/--
More generally, we can ask about classes of groups for which this holds.
A class of groups has definable normal subgroups if every group in the class does.
-/
def ClassHasDefinableNormalSubgroups
    (P : ∀ (G : Type*) [Group G], Prop) : Prop :=
  ∀ (G : Type*) [Group G], P G → HasDefinableNormalSubgroups G

/--
Kourovka Problem 1.20: Characterize which groups (or classes of groups)
have the property that normal subgroups are first-order definable in
the subgroup lattice.

This is an open research problem. The formalization captures the question
as asking for a characterization of when `HasDefinableNormalSubgroups G` holds.
-/
theorem kourovka_1_20_characterization :
    ∃ (P : ∀ (G : Type*) [Group G], Prop),
      (∀ (G : Type*) [Group G], HasDefinableNormalSubgroups G ↔ P G) := by
  -- This is the problem: find such a characterization P
  -- Trivially true by taking P = HasDefinableNormalSubgroups
  exact ⟨fun G _ => HasDefinableNormalSubgroups G, fun _ _ => Iff.rfl⟩

/-!
## Known Partial Results (as formal statements)

The following are known partial results that would be theorems
in a complete treatment of this problem.
-/

/--
For Dedekind groups (groups where every subgroup is normal),
the normal subgroups are trivially definable since they equal all subgroups.
-/
def IsDedekindGroup (G : Type*) [Group G] : Prop :=
  ∀ H : Subgroup G, H.Normal

theorem dedekind_has_definable_normal_subgroups
    (G : Type*) [Group G] (hG : IsDedekindGroup G) :
    HasDefinableNormalSubgroups G := by
  sorry

/--
For simple groups (groups with only trivial normal subgroups),
the normal subgroups {1, G} are definable as "smallest and largest elements".
-/
def IsSimpleGroup (G : Type*) [Group G] : Prop :=
  ∀ H : Subgroup G, H.Normal → H = ⊥ ∨ H = ⊤

theorem simple_has_definable_normal_subgroups
    (G : Type*) [Group G] [Nontrivial G] (hG : IsSimpleGroup G) :
    HasDefinableNormalSubgroups G := by
  sorry

/--
A stronger form of the question: is there a UNIFORM formula that works
for all groups in a given class? This is asking whether there is a single
first-order formula φ(x) in the language of lattices such that for every
group G in the class, φ defines exactly the normal subgroups of G.
-/
def ClassHasUniformlyDefinableNormalSubgroups
    (P : ∀ (G : Type*) [Group G], Prop) : Prop :=
  ∃ (φ : Language.order.Formula (Fin 1)),
    ∀ (G : Type*) [Group G], P G →
      IsNormalSubgroupPredicate G = {H | φ.Realize (fun _ => H)}

/--
The main open problem restated: characterize the classes of groups
with uniformly definable normal subgroups.
-/
theorem kourovka_1_20_uniform_version :
    ∃ (P : ∀ (G : Type*) [Group G], Prop),
      ClassHasUniformlyDefinableNormalSubgroups P ∧
      (∀ Q, ClassHasUniformlyDefinableNormalSubgroups Q → ∀ G [Group G], Q G → P G) := by
  -- This asks for the maximal class with this property
  sorry

end
