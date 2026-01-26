/-
Kourovka Notebook Problem 1.31 (M. I. Kargapolov)

Is a residually finite group with the maximum condition for subgroups almost polycyclic?

Key Definitions:
- Residually finite: For every non-identity element g, there exists a normal subgroup N
  of finite index such that g ∉ N
- Maximum condition for subgroups: Every ascending chain of subgroups stabilizes
  (equivalently, WellFoundedGT on the lattice of subgroups)
- Polycyclic: A group with a subnormal series where all factors are cyclic
- Almost polycyclic (virtually polycyclic): Has a polycyclic subgroup of finite index
-/

import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Order.WellFounded

/-! ## Residually Finite Groups -/

/--
A group is **residually finite** if for every non-identity element g,
there exists a normal subgroup of finite index not containing g.

Equivalently: the intersection of all normal subgroups of finite index is trivial.
-/
def IsResiduallyFinite (G : Type*) [Group G] : Prop :=
  ∀ g : G, g ≠ 1 → ∃ N : Subgroup G, N.Normal ∧ N.FiniteIndex ∧ g ∉ N

/-! ## Maximum Condition for Subgroups -/

/--
A group satisfies the **maximum condition for subgroups** (also called ACC or
Noetherian condition on subgroups) if every ascending chain of subgroups stabilizes.

This is equivalent to `WellFoundedGT (Subgroup G)`.
-/
def HasMaxConditionSubgroups (G : Type*) [Group G] : Prop :=
  WellFoundedGT (Subgroup G)

/-! ## Polycyclic Groups -/

/--
A **subnormal series** in a group G is a finite descending chain of subgroups
⊤ = G₀ ⊵ G₁ ⊵ ... ⊵ Gₙ = ⊥
where each Gᵢ₊₁ is normal in Gᵢ.

We use a structure that captures:
- A finite sequence of subgroups indexed by Fin (n+1)
- Starting at ⊤ and ending at ⊥
- Each term is normal in the previous
-/
structure SubnormalSeries (G : Type) [Group G] where
  /-- The length n of the series (number of proper inclusions) -/
  length : ℕ
  /-- The sequence of subgroups, with chain(0) = ⊤ and chain(length) = ⊥ -/
  chain : Fin (length + 1) → Subgroup G
  /-- The series starts at ⊤ -/
  starts_top : chain ⟨0, Nat.zero_lt_succ length⟩ = ⊤
  /-- The series ends at ⊥ -/
  ends_bot : chain ⟨length, Nat.lt_succ_self length⟩ = ⊥
  /-- The series is descending -/
  descending : ∀ i : Fin length, chain i.succ ≤ chain i.castSucc
  /-- Each term is normal in the previous -/
  normal : ∀ i : Fin length, (chain i.succ).subgroupOf (chain i.castSucc) |>.Normal

/--
The factor (quotient) at position i in a subnormal series.
This is Gᵢ / Gᵢ₊₁ where the series is G₀ ⊵ G₁ ⊵ ... ⊵ Gₙ.
-/
def SubnormalSeries.factor {G : Type} [Group G] (s : SubnormalSeries G)
    (i : Fin s.length) : Type :=
  ↥(s.chain i.castSucc) ⧸ (s.chain i.succ).subgroupOf (s.chain i.castSucc)

/-- The factor of a subnormal series has a group structure -/
instance SubnormalSeries.factorGroup {G : Type} [Group G] (s : SubnormalSeries G)
    (i : Fin s.length) : Group (s.factor i) :=
  @QuotientGroup.Quotient.group _ _ _ (s.normal i)

/--
A group is **polycyclic** if it has a subnormal series where all successive
quotients are cyclic.

More precisely, G is polycyclic if there exists a subnormal series
⊤ = G₀ ⊵ G₁ ⊵ ... ⊵ Gₙ = ⊥
such that each quotient Gᵢ/Gᵢ₊₁ is cyclic.
-/
def IsPolycyclic (G : Type) [Group G] : Prop :=
  ∃ (s : SubnormalSeries G), ∀ i : Fin s.length,
    @IsCyclic (s.factor i) (DivInvMonoid.toZPow (M := s.factor i))

/-! ## Almost Polycyclic (Virtually Polycyclic) Groups -/

/--
A group is **almost polycyclic** (or **virtually polycyclic**) if it contains
a polycyclic subgroup of finite index.
-/
def IsAlmostPolycyclic (G : Type) [Group G] : Prop :=
  ∃ H : Subgroup G, H.FiniteIndex ∧ IsPolycyclic H

/-! ## The Main Problem -/

/--
**Kourovka Notebook Problem 1.31** (M. I. Kargapolov):

Is a residually finite group with the maximum condition for subgroups almost polycyclic?

This is asking whether the conjunction of:
1. Residually finite
2. Maximum condition for subgroups (ACC on subgroups)

implies that the group is almost polycyclic (virtually polycyclic).

Note: This problem was answered positively. A residually finite group with the
maximum condition for subgroups is indeed almost polycyclic.
-/
theorem kourovka_1_31 (G : Type) [Group G]
    (hRes : IsResiduallyFinite G)
    (hMax : HasMaxConditionSubgroups G) :
    IsAlmostPolycyclic G := by
  sorry

/--
Alternative formulation as a question: Does there exist a counterexample?

A counterexample would be a group that is both residually finite and has the
maximum condition for subgroups, but is NOT almost polycyclic.

The theorem `kourovka_1_31` asserts no such counterexample exists.
-/
def kourovka_1_31_counterexample_exists : Prop :=
  ∃ (G : Type) (_ : Group G),
    IsResiduallyFinite G ∧ HasMaxConditionSubgroups G ∧ ¬IsAlmostPolycyclic G

/-- The positive answer to Problem 1.31 is equivalent to no counterexample existing -/
theorem kourovka_1_31_equiv_no_counterexample :
    (∀ (G : Type) [Group G], IsResiduallyFinite G → HasMaxConditionSubgroups G →
      IsAlmostPolycyclic G) ↔ ¬kourovka_1_31_counterexample_exists := by
  constructor
  · intro h ⟨G, hGrp, hRes, hMax, hNot⟩
    exact hNot (h G hRes hMax)
  · intro h G _ hRes hMax
    by_contra hNot
    apply h
    exact ⟨G, inferInstance, hRes, hMax, hNot⟩
