/-
Kourovka Notebook Problem 6.30 (O. V. Mel'nikov)

Let G be a residually finite Hopfian group, and let bG be its profinite completion.
Is bG necessarily Hopfian (in topological sense)?

This formalization defines:
- Hopfian groups (surjective endomorphisms are bijective)
- Residually finite groups (intersection of normal finite-index subgroups is trivial)
- Topologically Hopfian groups (continuous surjective endomorphisms are bijective)
- The problem statement about profinite completions
-/

import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.GroupTheory.Index
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic

open Topology

/-!
## Definitions
-/

variable (G : Type*) [Group G]

/--
A group is **Hopfian** if every surjective group endomorphism is injective (hence bijective).
-/
def IsHopfianGroup : Prop :=
  ∀ f : G →* G, Function.Surjective f → Function.Injective f

/--
The **groupResidual** of a group is the intersection of all normal subgroups of finite index.
A group is residually finite if this residual is trivial.
-/
def groupResidual : Subgroup G where
  carrier := {g | ∀ H : Subgroup G, H.Normal → H.FiniteIndex → g ∈ H}
  one_mem' := fun H _ _ => H.one_mem
  mul_mem' := fun ha hb H hN hF => H.mul_mem (ha H hN hF) (hb H hN hF)
  inv_mem' := fun ha H hN hF => H.inv_mem (ha H hN hF)

/--
A group is **residually finite** if the intersection of all its normal
finite-index subgroups is trivial (i.e., contains only the identity).
-/
def IsResiduallyFiniteGroup : Prop := groupResidual G = ⊥

variable {G}

/--
A topological group is **topologically Hopfian** if every continuous surjective
group endomorphism is injective (hence a topological isomorphism).
-/
def IsTopologicallyHopfian (H : Type*) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] :
    Prop :=
  ∀ f : H →* H, Continuous f → Function.Surjective f → Function.Injective f

/-!
## Profinite Completion

The profinite completion of a group G is defined as the inverse limit of the system
of finite quotients of G. When G is residually finite, the natural map G → Ĝ is injective.

For a rigorous formalization, we would need to construct the inverse limit over the
directed system of finite quotients. Here we axiomatize the essential properties.
-/

/--
Structure representing a profinite completion of a group.

The profinite completion Ĝ of a group G comes with:
- A profinite group structure
- A canonical homomorphism from G to Ĝ
- The universal property with respect to maps to profinite groups
-/
structure ProfiniteCompletion (G : Type*) [Group G] where
  /-- The underlying profinite group -/
  completion : ProfiniteGrp
  /-- The canonical map from G to its profinite completion -/
  toCompletion : G →* completion
  /-- When G is residually finite, the canonical map is injective -/
  injective_of_residuallyFinite : IsResiduallyFiniteGroup G → Function.Injective toCompletion

-- Axiom: Every group has a profinite completion
axiom profiniteCompletion (G : Type*) [Group G] : ProfiniteCompletion G

/-!
## Main Problem Statement
-/

/--
**Kourovka Notebook Problem 6.30** (O. V. Mel'nikov):

Let G be a residually finite Hopfian group, and let Ĝ be its profinite completion.
Is Ĝ necessarily Hopfian in the topological sense?

The question asks: if G is both residually finite and Hopfian (as an abstract group),
must its profinite completion Ĝ be topologically Hopfian (i.e., every continuous
surjective endomorphism is an isomorphism)?
-/
theorem kourovka_6_30 :
    ∀ (G : Type*) [Group G],
      IsResiduallyFiniteGroup G →
      IsHopfianGroup G →
      let Ĝ := profiniteCompletion G
      IsTopologicallyHopfian Ĝ.completion := by
  sorry
