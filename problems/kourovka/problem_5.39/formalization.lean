/-
Kourovka Notebook Problem 5.39 (P. M. Neumann)

Prove that every countable group can act faithfully as a group of automorphisms
of a finitely generated soluble group (of derived length at most 4).

This asks to prove that for any countable group G, there exists a finitely generated
solvable group H with derived length ≤ 4 such that G embeds into Aut(H).

For background to this problem, in particular its relationship with problem 8.50,
see (P. M. Neumann, in: Groups–Korea, Pusan, 1988 (Lect. Notes Math., 1398),
Springer, Berlin, 1989, 124–139).
-/

import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.Finiteness
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Data.Countable.Defs

/--
A group has derived length at most n if its n-th derived subgroup is trivial.
In particular, this means the group is solvable.
-/
def hasDerivedLengthAtMost (G : Type*) [Group G] (n : ℕ) : Prop :=
  derivedSeries G n = ⊥

/--
A group action of G on H by automorphisms.
This corresponds to a group homomorphism G →* MulAut H.
-/
def ActsByAutomorphisms (G H : Type*) [Group G] [Group H] : Prop :=
  Nonempty (G →* MulAut H)

/--
A group G acts **faithfully** on H by automorphisms if there exists an
injective group homomorphism G →* MulAut H.
-/
def ActsFaithfullyByAutomorphisms (G H : Type*) [Group G] [Group H] : Prop :=
  ∃ (φ : G →* MulAut H), Function.Injective φ

/--
**Kourovka Problem 5.39** (P. M. Neumann):

Every countable group can act faithfully as a group of automorphisms
of a finitely generated solvable group of derived length at most 4.
-/
theorem kourovka_5_39
    (G : Type*) [Group G] [Countable G] :
    ∃ (H : Type) (_ : Group H) (_ : Group.FG H) (_ : IsSolvable H),
      hasDerivedLengthAtMost H 4 ∧ ActsFaithfullyByAutomorphisms G H := by
  sorry

/-!
## Discussion

This is a constructive existence problem: given any countable group G,
we must construct a finitely generated solvable group H with derived length ≤ 4
and exhibit a faithful action of G on H by automorphisms.

The derived length bound of 4 is significant - it means H is metabelian-by-metabelian.

This result shows that the automorphism groups of finitely generated solvable groups
are "universal" in the sense that every countable group embeds into one of them.

Related to Problem 8.50 in the Kourovka Notebook, which concerns the relationship
between faithful actions and embedding problems.
-/
