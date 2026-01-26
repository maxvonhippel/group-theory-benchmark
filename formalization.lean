/-
Kourovka Notebook Problem 1.12 (W. Magnus)

"The problem of the isomorphism to the trivial group for all groups with n generators
and n defining relations, where n > 2."

## Problem Analysis

This problem asks about the **decidability** of determining whether a balanced group
presentation (n generators and n relations) presents the trivial group, for n > 2.

This is fundamentally a **meta-mathematical question** about the existence of algorithms.
It asks: "Is there an algorithm that, given any finite balanced presentation
⟨x₁,...,xₙ | r₁,...,rₙ⟩ with n > 2, decides whether the presented group is trivial?"

## Formalization Approach

We formalize the underlying mathematical objects:
1. Balanced presentations (n generators, n relations)
2. The triviality condition for such presentations
3. The decidability question as a type-theoretic statement

The statement `∀ P, Decidable (P.isTrivial)` captures the decidability question:
- If this type is inhabited, the problem is decidable
- If this type is uninhabited, the problem is undecidable

## Historical Context

This is related to the word problem for groups. The triviality problem is known to be
undecidable in general. The status for the restricted case of balanced presentations
was the subject of this problem. (Note: This was later resolved - the problem IS
undecidable even for balanced presentations when n is large enough.)
-/

import Mathlib.GroupTheory.PresentedGroup
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.Data.Fin.Basic

open FreeGroup

/--
A **balanced presentation** with `n` generators consists of exactly `n` relations,
where each relation is an element of the free group on `n` generators.

This represents a group presentation ⟨x₁, ..., xₙ | r₁, ..., rₙ⟩.
-/
structure BalancedPresentation (n : ℕ) where
  /-- The n relations, each an element of the free group on Fin n -/
  relations : Fin n → FreeGroup (Fin n)

/-- The group presented by a balanced presentation -/
def BalancedPresentation.toGroup {n : ℕ} (P : BalancedPresentation n) : Type :=
  PresentedGroup (Set.range P.relations)

instance {n : ℕ} (P : BalancedPresentation n) : Group P.toGroup :=
  PresentedGroup.instGroup _

/--
A balanced presentation is **trivial** if the group it presents has exactly one element.
Equivalently, every element of the free group becomes the identity in the quotient.
-/
def BalancedPresentation.isTrivial {n : ℕ} (P : BalancedPresentation n) : Prop :=
  Subsingleton P.toGroup

/--
**Kourovka Notebook Problem 1.12** (W. Magnus)

The problem asks: For n > 2, is the triviality problem decidable for balanced
presentations with n generators and n relations?

Formally: Does there exist a decision procedure that, for any balanced presentation
P with n > 2, determines whether P presents the trivial group?

## Type-Theoretic Interpretation

This is stated as asking for a term of type:
`∀ n > 2, ∀ P : BalancedPresentation n, Decidable P.isTrivial`

- If such a term can be constructed, the triviality problem is decidable
- If no such term exists (the type is uninhabited), the problem is undecidable

The `sorry` here represents the open nature of the problem at the time it was posed.
(The problem has since been resolved: it is undecidable for sufficiently large n.)
-/
def kourovka_1_12 :
    (n : ℕ) → n > 2 → (P : BalancedPresentation n) → Decidable P.isTrivial := by
  sorry
