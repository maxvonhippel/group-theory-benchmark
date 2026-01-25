/-
Kourovka Notebook Problem 1.35c (A. I. Mal'cev, L. Fuchs)

Do there exist simple pro-orderable groups?

A group is said to be pro-orderable if each of its partial orderings
(compatible with the group operation) can be extended to a linear ordering
(also compatible with the group operation).

Attribution: M. I. Kargapolov

Historical context:
- A partial ordering on a group G is compatible if it is translation-invariant:
  a ≤ b implies c * a ≤ c * b and a * c ≤ b * c for all c
- Pro-orderable groups form a proper subclass of groups
- Simple groups have no proper non-trivial normal subgroups
- The intersection of these classes is the subject of this problem
-/

import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.Order.Extension.Linear
import Mathlib.Algebra.Order.Group.Defs

/--
A partial order on a group G is called left-invariant if
left multiplication preserves the order: a ≤ b → c * a ≤ c * b
-/
def IsLeftInvariant {G : Type*} [Group G] (le : G → G → Prop) : Prop :=
  ∀ a b c : G, le a b → le (c * a) (c * b)

/--
A partial order on a group G is called right-invariant if
right multiplication preserves the order: a ≤ b → a * c ≤ b * c
-/
def IsRightInvariant {G : Type*} [Group G] (le : G → G → Prop) : Prop :=
  ∀ a b c : G, le a b → le (a * c) (b * c)

/--
A partial order on a group G is translation-invariant (bi-invariant) if
it is both left-invariant and right-invariant.
This is the standard notion of a group-compatible partial order.
-/
def IsTranslationInvariant {G : Type*} [Group G] (le : G → G → Prop) : Prop :=
  IsLeftInvariant le ∧ IsRightInvariant le

/--
A partial ordering structure on G that is compatible with the group operation.
This captures the notion of "a partial ordering on the group" in the problem.
-/
structure GroupPartialOrder (G : Type*) [Group G] where
  /-- The partial order relation -/
  le : G → G → Prop
  /-- Reflexivity -/
  le_refl : ∀ a, le a a
  /-- Antisymmetry -/
  le_antisymm : ∀ a b, le a b → le b a → a = b
  /-- Transitivity -/
  le_trans : ∀ a b c, le a b → le b c → le a c
  /-- Left translation invariance -/
  left_inv : ∀ a b c, le a b → le (c * a) (c * b)
  /-- Right translation invariance -/
  right_inv : ∀ a b c, le a b → le (a * c) (b * c)

/--
A linear ordering structure on G that is compatible with the group operation.
-/
structure GroupLinearOrder (G : Type*) [Group G] extends GroupPartialOrder G where
  /-- Totality: any two elements are comparable -/
  le_total : ∀ a b, le a b ∨ le b a

/--
A partial order P extends to a linear order Q if Q agrees with P where P is defined.
Specifically, whenever P says a ≤ b, Q also says a ≤ b.
-/
def GroupPartialOrder.ExtendsTo {G : Type*} [Group G]
    (P : GroupPartialOrder G) (Q : GroupLinearOrder G) : Prop :=
  ∀ a b, P.le a b → Q.le a b

/--
A group G is pro-orderable if every group-compatible partial order on G
can be extended to a group-compatible linear order on G.

This is the key definition from the problem statement.
-/
def IsProOrderable (G : Type*) [Group G] : Prop :=
  ∀ (P : GroupPartialOrder G), ∃ (Q : GroupLinearOrder G), P.ExtendsTo Q

/--
Kourovka Problem 1.35c: Do there exist simple pro-orderable groups?

The problem asks for the existence of a group G that is:
1. Simple (no proper non-trivial normal subgroups)
2. Pro-orderable (every compatible partial order extends to a compatible linear order)

A positive answer would provide such a group.
A negative answer would prove no such group exists.
-/
theorem kourovka_1_35c :
    (∃ (G : Type) (_ : Group G) (_ : IsSimpleGroup G), IsProOrderable G) ∨
    (∀ (G : Type) [Group G] [IsSimpleGroup G], ¬ IsProOrderable G) := by
  sorry

/--
Alternative formulation: Statement that simple pro-orderable groups exist.
-/
def SimpleProOrderableGroupExists : Prop :=
  ∃ (G : Type) (_ : Group G) (_ : IsSimpleGroup G), IsProOrderable G

/--
Alternative formulation: Statement that no simple pro-orderable groups exist.
-/
def NoSimpleProOrderableGroup : Prop :=
  ∀ (G : Type) [Group G] [IsSimpleGroup G], ¬ IsProOrderable G

/--
The problem has a definite answer: exactly one of these holds.
-/
theorem kourovka_1_35c_exclusive :
    SimpleProOrderableGroupExists ↔ ¬ NoSimpleProOrderableGroup := by
  unfold SimpleProOrderableGroupExists NoSimpleProOrderableGroup
  constructor
  · intro ⟨G, hG, hSimple, hPro⟩ hNo
    exact @hNo G hG hSimple hPro
  · intro h
    push_neg at h
    obtain ⟨G, hG, hSimple, hPro⟩ := h
    exact ⟨G, hG, hSimple, hPro⟩

/-!
## Notes on the problem

This is an open existence problem from 1965. The key concepts are:

1. **Simple groups**: Groups with no proper non-trivial normal subgroups.
   Examples include cyclic groups of prime order and alternating groups A_n (n ≥ 5).

2. **Pro-orderable groups**: Groups where every partial order compatible with
   the group operation can be extended to a total order. This is stronger than
   merely being orderable (having some compatible total order).

3. **The intersection**: The question asks whether these two properties can
   coexist. Simple groups are "algebraically simple" while pro-orderability
   is an "order-theoretic richness" property.

The formalization captures the precise mathematical question without resolving it.
-/
