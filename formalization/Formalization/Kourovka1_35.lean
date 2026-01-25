/-
Kourovka Notebook Problem 1.35c (A. I. Mal'cev, L. Fuchs)

Do there exist simple pro-orderable groups?

A group is said to be **pro-orderable** if each of its partial orderings can be extended
to a linear ordering.

Here, a "partial ordering" on a group means a partial order that is compatible with the
group operation: if a ≤ b then ca ≤ cb and ac ≤ bc for all c.
-/

import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.Order.Extension.Linear

open Set

/--
A **group partial order** on G is a partial order that is compatible with the group operation
on both sides: if a ≤ b then ca ≤ cb and ac ≤ bc for all c.

This is the standard definition of a partial ordering of a group (also called a
"translation-invariant partial order").
-/
structure GroupPartialOrder (G : Type*) [Group G] where
  /-- The underlying partial order relation -/
  le : G → G → Prop
  /-- Reflexivity -/
  le_refl : ∀ a, le a a
  /-- Transitivity -/
  le_trans : ∀ a b c, le a b → le b c → le a c
  /-- Antisymmetry -/
  le_antisymm : ∀ a b, le a b → le b a → a = b
  /-- Left translation invariance: a ≤ b implies ca ≤ cb -/
  mul_le_mul_left : ∀ a b c, le a b → le (c * a) (c * b)
  /-- Right translation invariance: a ≤ b implies ac ≤ bc -/
  mul_le_mul_right : ∀ a b c, le a b → le (a * c) (b * c)

/--
A **group linear order** on G is a linear order that is compatible with the group operation.
-/
structure GroupLinearOrder (G : Type*) [Group G] extends GroupPartialOrder G where
  /-- Totality: for any two elements, one is ≤ the other -/
  le_total : ∀ a b, le a b ∨ le b a

/--
A group partial order P₁ **extends** another P₂ if whenever P₂.le a b, we have P₁.le a b.
-/
def GroupPartialOrder.Extends {G : Type*} [Group G] (P₁ P₂ : GroupPartialOrder G) : Prop :=
  ∀ a b, P₂.le a b → P₁.le a b

/--
A group is **pro-orderable** if every group partial order on it can be extended to
a group linear order.

In other words, for any partial ordering compatible with the group operation,
there exists a linear ordering compatible with the group operation that extends it.
-/
def IsProOrderable (G : Type*) [Group G] : Prop :=
  ∀ (P : GroupPartialOrder G), ∃ (L : GroupLinearOrder G), L.toGroupPartialOrder.Extends P

/--
**Kourovka Notebook Problem 1.35c** (A. I. Mal'cev, L. Fuchs; M. I. Kargapolov):

Do there exist simple pro-orderable groups?

The question asks whether there exists a group G that is both:
1. Simple (has no proper nontrivial normal subgroups)
2. Pro-orderable (every partial ordering can be extended to a linear ordering)

Note: The trivial group is pro-orderable but not simple (simple groups must be nontrivial).
-/
theorem kourovka_1_35c :
    ∃ (G : Type*) (_ : Group G), IsSimpleGroup G ∧ IsProOrderable G := by
  sorry
