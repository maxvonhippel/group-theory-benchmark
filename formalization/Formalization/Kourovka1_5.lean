/-
Kourovka Notebook Problem 1.5 (L. A. Bokut')

(Well-known problem). Does there exist a group whose group ring does not
contain zero divisors and is not embeddable into a skew field?

This is related to the Malcev problem: A domain (ring without zero divisors)
that cannot be embedded into a division ring (skew field).

The group ring here is implicitly over ℤ (the integers), as is standard
in the Kaplansky conjecture context.
-/

import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Ring.Hom.Defs

/-- The group ring Z[G] is the monoid algebra of G over Z -/
abbrev GroupRingZ (G : Type*) [Group G] := MonoidAlgebra ℤ G

/-- A ring is embeddable into a division ring if there exists an injective ring homomorphism
    from it into some division ring -/
def IsEmbeddableIntoDivisionRing (R : Type*) [Ring R] : Prop :=
  ∃ (D : Type) (_ : DivisionRing D) (f : R →+* D), Function.Injective f

/--
Kourovka Problem 1.5: Malcev's Embedding Problem for Group Rings

The problem asks: Does there exist a group G such that:
1. The group ring Z[G] has no zero divisors (is a domain)
2. The group ring Z[G] cannot be embedded into any division ring (skew field)

A positive answer would give a counterexample to the conjecture that
every domain is embeddable into a division ring.
-/
def kourovka_1_5_positive_answer : Prop :=
  ∃ (G : Type) (_ : Group G),
    NoZeroDivisors (GroupRingZ G) ∧ ¬ IsEmbeddableIntoDivisionRing (GroupRingZ G)

/--
The negative answer to Problem 1.5 would mean:
Every group ring Z[G] that has no zero divisors is embeddable into a division ring.
-/
def kourovka_1_5_negative_answer : Prop :=
  ∀ (G : Type) [Group G],
    NoZeroDivisors (GroupRingZ G) → IsEmbeddableIntoDivisionRing (GroupRingZ G)

/-- The positive and negative answers are negations of each other -/
theorem kourovka_1_5_dichotomy :
    kourovka_1_5_positive_answer ↔ ¬ kourovka_1_5_negative_answer := by
  unfold kourovka_1_5_positive_answer kourovka_1_5_negative_answer
  constructor
  · intro ⟨G, hGrp, hNZD, hNotEmbed⟩ hNeg
    exact hNotEmbed (hNeg G hNZD)
  · intro hNotNeg
    by_contra hContra
    push_neg at hContra
    apply hNotNeg
    intro G _ hNZD
    exact hContra G inferInstance hNZD

/--
Historical note: This problem was answered positively by A. I. Malcev (1937)
who constructed examples of non-commutative domains that cannot be embedded
into division rings. However, the specific question for *group rings* of groups
is more subtle and relates to orderability of groups.

For a torsion-free group G, if G is bi-orderable (left-orderable), then Z[G]
embeds into a division ring. So a counterexample would require a group G such that:
1. Z[G] has no zero divisors (conjecturally true for all torsion-free groups)
2. G is not bi-orderable

Whether such a group exists with Z[G] being a domain but not embeddable
into a division ring remains an important open question.
-/
theorem kourovka_1_5_open_problem :
    kourovka_1_5_positive_answer ∨ kourovka_1_5_negative_answer := by
  sorry
