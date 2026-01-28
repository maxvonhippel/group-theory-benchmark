/-
Kourovka Notebook Problem 3.12 (Well-known problem) (Yu. M. Gorchakov)

Is a locally finite group with a full Sylow basis locally soluble?

Definitions:
- A group is locally finite if every finitely generated subgroup is finite.
- A Sylow basis is a set of Sylow p-subgroups, one for each prime p dividing |G|,
  such that any two subgroups in the basis permute (PQ = QP).
- A full Sylow basis includes a Sylow p-subgroup for every prime p.
- A group is locally soluble if every finitely generated subgroup is soluble.
-/

import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.Finiteness
import Mathlib.Data.Nat.Prime.Defs

variable {G : Type*} [Group G]

/-- A group is locally finite if every finitely generated subgroup is finite -/
def IsLocallyFinite (G : Type*) [Group G] : Prop :=
  ∀ H : Subgroup G, H.FG → Finite H

/-- A group is locally soluble if every finitely generated subgroup is soluble -/
def IsLocallySoluble (G : Type*) [Group G] : Prop :=
  ∀ H : Subgroup G, H.FG → IsSolvable H

/-- Two subgroups permute if their setwise product equals their join -/
def Subgroup.Permutes (H K : Subgroup G) : Prop :=
  ∀ h : G, h ∈ H → ∀ k : G, k ∈ K → ∃ k' ∈ K, ∃ h' ∈ H, h * k = k' * h'

/--
A Sylow basis for a group is a family of Sylow p-subgroups (indexed by primes p)
such that any two subgroups in the family permute.
-/
structure SylowBasis (G : Type*) [Group G] where
  /-- For each prime p, we have a Sylow p-subgroup -/
  subgroup : (p : Nat) → [Fact (Nat.Prime p)] → Sylow p G
  /-- Any two subgroups in the basis permute -/
  permutes : ∀ (p q : Nat) [Fact (Nat.Prime p)] [Fact (Nat.Prime q)],
    Subgroup.Permutes (subgroup p).toSubgroup (subgroup q).toSubgroup

/--
A full Sylow basis is a Sylow basis where, for every prime p, the Sylow p-subgroup
is specified (which is automatic from our definition, as Sylow p G is always nonempty
for any prime p in a group G).
-/
abbrev FullSylowBasis (G : Type*) [Group G] := SylowBasis G

/--
Kourovka Problem 3.12: Is a locally finite group with a full Sylow basis locally soluble?

This asks whether the existence of a full Sylow basis in a locally finite group
implies that the group is locally soluble.
-/
theorem kourovka_3_12
    (G : Type*) [Group G]
    (hLF : IsLocallyFinite G)
    (hBasis : FullSylowBasis G) :
    IsLocallySoluble G := by
  sorry

/--
Alternative formulation as an implication statement.
-/
def kourovka_3_12_statement : Prop :=
  ∀ (G : Type) [Group G],
    IsLocallyFinite G → FullSylowBasis G → IsLocallySoluble G
