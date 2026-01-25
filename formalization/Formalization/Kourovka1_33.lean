/-
Kourovka Notebook Problem 1.33 (A. I. Mal'cev)

Describe the automorphism group of a free solvable group.

A free solvable group of rank n and derived length k is the quotient of the
free group F_n by its k-th derived subgroup: F_n^(k) = F_n / D^k(F_n).

This is a description problem rather than a yes/no question. The formalization
captures the objects involved and states what a "description" would entail:
characterizing the structure of Aut(F_n^(k)) in terms of more familiar groups.

Historical context:
- For k = 1 (free abelian groups), Aut(Z^n) ≅ GL_n(Z)
- For k = 2 (free metabelian groups), significant progress was made by
  Bachmuth, Mochizuki, and others
- The general problem involves understanding the kernel of the natural
  homomorphism Aut(F_n^(k)) → Aut(F_n^(k-1)) (the IA-automorphisms)
-/

import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.Algebra.Group.End

open Subgroup

/--
The free solvable group of rank n and derived length k is the quotient of
the free group on n generators by its k-th derived subgroup.

This is the largest solvable quotient of the free group with derived length ≤ k.
-/
def FreeSolvableGroup (n : ℕ) (k : ℕ) : Type :=
  (FreeGroup (Fin n)) ⧸ (derivedSeries (FreeGroup (Fin n)) k)

instance (n k : ℕ) : Group (FreeSolvableGroup n k) :=
  QuotientGroup.Quotient.group _

/--
The free solvable group of derived length k is solvable.
-/
theorem freeSolvableGroup_isSolvable (n k : ℕ) : IsSolvable (FreeSolvableGroup n k) := by
  sorry

/--
The automorphism group of a group G is the group of bijective homomorphisms G → G.
In Mathlib this is MulAut G.
-/
abbrev AutGroup (G : Type*) [Group G] := MulAut G

/--
For k = 1, the free solvable group F_n^(1) is isomorphic to the free abelian group Z^n.
This is because the first derived subgroup of F_n is its commutator, and
F_n / [F_n, F_n] ≅ Z^n.
-/
theorem freeSolvable_one_is_abelian (n : ℕ) :
    ∀ (x y : FreeSolvableGroup n 1), x * y = y * x := by
  sorry

/--
Natural projection from a free solvable group of derived length k+1
to one of derived length k.

This exists because D^(k+1)(F_n) ⊆ D^k(F_n), so there's a natural quotient map.
-/
def freeSolvableProjection (n k : ℕ) :
    FreeSolvableGroup n (k + 1) →* FreeSolvableGroup n k := by
  sorry

/--
The natural projection induces a homomorphism on automorphism groups:
Any automorphism of F_n^(k+1) induces an automorphism of F_n^(k).
-/
def autProjection (n k : ℕ) :
    AutGroup (FreeSolvableGroup n (k + 1)) →* AutGroup (FreeSolvableGroup n k) := by
  sorry

/--
The kernel of the automorphism projection consists of automorphisms that
act trivially on the lower derived quotient. These are sometimes called
"IA-automorphisms" (Identity on Abelianization when k = 0).
-/
def IAAutomorphisms (n k : ℕ) : Subgroup (AutGroup (FreeSolvableGroup n (k + 1))) :=
  (autProjection n k).ker

/--
A complete description of Aut(F_n^(k)) would involve:
1. Understanding the image of autProjection (which automorphisms of F_n^(k-1) lift)
2. Understanding the kernel IAAutomorphisms (what are the IA-automorphisms)
3. Understanding how these fit together (is there a split exact sequence?)

The problem is considered solved if we can characterize these in terms of
explicit generators and relations, or in terms of well-understood groups.
-/
structure FreeSolvableAutDescription (n k : ℕ) where
  /-- The image of the projection Aut(F_n^(k)) → Aut(F_n^(k-1)) -/
  image_characterized : Prop
  /-- The kernel (IA-automorphisms) is characterized -/
  kernel_characterized : Prop
  /-- The extension structure is understood -/
  extension_understood : Prop

/--
Kourovka Problem 1.33: The problem asks for a complete description of
Aut(FreeSolvableGroup n k) for all n and k.

A solution would provide a FreeSolvableAutDescription for all n, k.
-/
def kourovka_1_33_solved : Prop :=
  ∀ (n k : ℕ), ∃ (desc : FreeSolvableAutDescription n k),
    desc.image_characterized ∧ desc.kernel_characterized ∧ desc.extension_understood

/--
Partial result: For the free metabelian group (k = 2), the automorphism group
has been substantially described.

The automorphism group sits in a short exact sequence:
1 → IA_n → Aut(F_n^(2)) → GL_n(Z) → 1

where IA_n is a finitely generated group (for n ≥ 2) whose structure has been
studied by Bachmuth, Mochizuki, Roman'kov, and others.
-/
theorem aut_free_metabelian_exact_sequence (n : ℕ) (hn : 2 ≤ n) :
    Function.Surjective (autProjection n 1) := by
  sorry

/-!
## Discussion

Kourovka Problem 1.33 is a **description problem** rather than a theorem with a
definite yes/no answer. The formalization above captures:

1. The definition of free solvable groups as quotients of free groups
2. The natural tower of quotient maps between free solvable groups of different lengths
3. The induced maps on automorphism groups
4. The key structural question: understanding the image and kernel of these maps

The problem has been partially solved:
- The case k = 1 (free abelian) is classical: Aut(Z^n) ≅ GL_n(Z)
- The case k = 2 (free metabelian) was substantially addressed by Bachmuth, Mochizuki,
  Roman'kov, and others in the 1970s-1980s
- General k remains of interest

A complete formalization of the "solution" would require formalizing the specific
structure theorems that describe these automorphism groups.
-/
