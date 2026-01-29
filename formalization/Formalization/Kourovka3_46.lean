/-
Kourovka Notebook Problem 3.46 (B. I. Plotkin)

Does there exist a group having more than one, but finitely many maximal
locally soluble normal subgroups?

Key Definitions:
- Locally soluble subgroup: A subgroup H is locally soluble if every finitely
  generated subgroup of H is soluble (solvable).
- Maximal locally soluble normal subgroup: A normal subgroup that is locally
  soluble and is maximal among all locally soluble normal subgroups.

The question asks whether there exists a group G such that the set of maximal
locally soluble normal subgroups of G has cardinality k for some 1 < k < ∞.
-/

import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.Finiteness
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Data.Set.Card

variable {G : Type*} [Group G]

/-- A subgroup H of G is locally soluble if every finitely generated
subgroup of H is soluble. -/
def Subgroup.IsLocallySoluble (H : Subgroup G) : Prop :=
  ∀ K : Subgroup H, K.FG → IsSolvable K

/-- The set of all normal subgroups of G that are locally soluble. -/
def locallySolubleNormalSubgroups (G : Type*) [Group G] : Set (Subgroup G) :=
  { H : Subgroup G | H.Normal ∧ H.IsLocallySoluble }

/-- A normal locally soluble subgroup H is maximal if it is maximal among
all normal locally soluble subgroups (not contained in any strictly larger one). -/
def IsMaximalLocallySolubleNormal (H : Subgroup G) : Prop :=
  H ∈ locallySolubleNormalSubgroups G ∧
  ∀ K : Subgroup G, K ∈ locallySolubleNormalSubgroups G → H ≤ K → H = K

/-- The set of all maximal locally soluble normal subgroups of G. -/
def maximalLocallySolubleNormalSubgroups (G : Type*) [Group G] : Set (Subgroup G) :=
  { H : Subgroup G | IsMaximalLocallySolubleNormal H }

/--
**Kourovka Problem 3.46** (B. I. Plotkin):

Does there exist a group having more than one, but finitely many maximal
locally soluble normal subgroups?

This theorem states the existence claim: there exists a group G such that
the set of maximal locally soluble normal subgroups is finite and contains
at least two distinct elements.
-/
theorem kourovka_3_46 :
    ∃ (G : Type*) (_ : Group G),
      (maximalLocallySolubleNormalSubgroups G).Finite ∧
      1 < (maximalLocallySolubleNormalSubgroups G).ncard := by
  sorry
