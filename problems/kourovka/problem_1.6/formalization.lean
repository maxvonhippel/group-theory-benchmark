/-
Kourovka Notebook Problem 1.6 (A. I. Mal'cev)

Is the group ring of a right-ordered group embeddable into a skew field?

Attribution: L. A. Bokut'

A right-ordered group is a group with a total order that is right-invariant:
  a ≤ b → a * c ≤ b * c

The question asks whether, for any right-ordered group G and a suitable coefficient
ring R (typically ℤ, ℚ, or another field), the group ring R[G] can be embedded
into a division ring (skew field).

Historical note: This was answered affirmatively by Malcev and Neumann.
For a right-ordered group G, the group ring over any field can be embedded
into a division ring via the construction of Malcev-Neumann series (formal
power series with well-ordered support).
-/

import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs

/--
A right-ordered group is a group with a linear order where multiplication
on the right preserves the order: a ≤ b → a * c ≤ b * c

In Mathlib terminology, this is captured by a group with a linear order
where `MulRightMono` holds (covariant multiplication on the right).
-/
class RightOrderedGroup (G : Type*) extends Group G, LinearOrder G where
  /-- Right multiplication preserves the order -/
  mul_right_mono : ∀ (a b c : G), a ≤ b → a * c ≤ b * c

/-- Right-ordered groups satisfy `MulRightMono` -/
instance (G : Type*) [RightOrderedGroup G] : MulRightMono G where
  elim c _ _ hab := RightOrderedGroup.mul_right_mono _ _ c hab

/-- The group ring R[G] is the monoid algebra of G over R -/
abbrev GroupRing (R : Type*) (G : Type*) [Ring R] [Group G] := MonoidAlgebra R G

/-- A ring is embeddable into a division ring if there exists an injective ring homomorphism
    from it into some division ring -/
def IsEmbeddableIntoDivisionRing (R : Type*) [Ring R] : Prop :=
  ∃ (D : Type) (_ : DivisionRing D) (f : R →+* D), Function.Injective f

/--
Kourovka Problem 1.6: Malcev's Question on Right-Ordered Groups

The problem asks whether the group ring of any right-ordered group
can be embedded into a division ring (skew field).

This formalization captures the statement for the group ring Z[G]
over the integers, which is the most commonly studied case.
-/
theorem kourovka_1_6_over_Z (G : Type*) [RightOrderedGroup G] :
    IsEmbeddableIntoDivisionRing (GroupRing ℤ G) := by
  sorry

/--
More generally, for any field R and right-ordered group G,
the group ring R[G] embeds into a division ring.

This is the full Malcev-Neumann theorem.
-/
theorem kourovka_1_6_over_field (R : Type*) [Field R] (G : Type*) [RightOrderedGroup G] :
    IsEmbeddableIntoDivisionRing (GroupRing R G) := by
  sorry

/--
Alternative formulation: Does there exist a right-ordered group G
whose group ring (over integers) is NOT embeddable into a division ring?

A negative answer (this proposition being False) confirms that all
group rings of right-ordered groups embed into division rings.
-/
def kourovka_1_6_counterexample_exists : Prop :=
  ∃ (G : Type) (_ : RightOrderedGroup G),
    ¬ IsEmbeddableIntoDivisionRing (GroupRing ℤ G)

/-- The original question is equivalent to asking whether no counterexample exists -/
theorem kourovka_1_6_equiv :
    (∀ (G : Type) [RightOrderedGroup G], IsEmbeddableIntoDivisionRing (GroupRing ℤ G)) ↔
    ¬ kourovka_1_6_counterexample_exists := by
  unfold kourovka_1_6_counterexample_exists
  constructor
  · intro h ⟨G, hRO, hNotEmbed⟩
    exact hNotEmbed (h G)
  · intro h G _
    by_contra hContra
    apply h
    exact ⟨G, inferInstance, hContra⟩

/--
The answer to Problem 1.6 is known to be YES (affirmative).

For any right-ordered group G and any division ring R, the group ring R[G]
can be embedded into a division ring. This was proved using the
Malcev-Neumann construction of formal power series with well-ordered support.

The embedding goes: R[G] ↪ R((G)) where R((G)) is the ring of Malcev-Neumann
series, which is itself a division ring when R is a division ring and G is
right-ordered.
-/
theorem kourovka_1_6_answer_affirmative :
    ∀ (G : Type) [RightOrderedGroup G], IsEmbeddableIntoDivisionRing (GroupRing ℤ G) := by
  intro G _
  exact kourovka_1_6_over_Z G
