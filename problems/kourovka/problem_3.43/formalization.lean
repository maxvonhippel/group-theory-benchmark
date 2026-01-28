/-
Kourovka Notebook Problem 3.43
B. I. Plotkin

Let μ be an infinite cardinal number. A group G is said to be μ-overnilpotent
if every cyclic subgroup of G is a member of some ascending normal series of
length less than μ reaching G.

It is not difficult to show that the class of μ-overnilpotent groups is a radical class.

Is it true that if μ₁ < μ₂ for two infinite cardinal numbers μ₁ and μ₂,
then there exists a group G which is μ₂-overnilpotent and μ₁-semisimple?

Remark of 2001: In (S. Vovsi, Sov. Math. Dokl., 13 (1972), 408–410) it was proved
that for any two infinite cardinals μ₁ < μ₂ there exists a group that is
μ₂-overnilpotent but not μ₁-overnilpotent.
-/

import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.GroupTheory.Subgroup.Simple

variable {G : Type*} [Group G]

/-- An ascending normal series indexed by ordinals less than α is a family of
normal subgroups {Hᵢ}_{i < α} such that:
- H₀ = ⊥
- Hᵢ ≤ Hⱼ for i ≤ j
- Each Hᵢ is normal in G
- For limit ordinals λ, H_λ = ⨆_{i < λ} Hᵢ -/
structure AscendingNormalSeries (G : Type*) [Group G] (α : Ordinal) where
  /-- The family of subgroups -/
  series : ∀ i : Ordinal, i < α → Subgroup G
  /-- Each member is normal in G -/
  normal : ∀ i (hi : i < α), (series i hi).Normal
  /-- The series is ascending -/
  mono : ∀ i j (hi : i < α) (hj : j < α), i ≤ j → series i hi ≤ series j hj

/-- A subgroup H is a member of an ascending normal series if H equals some
member of the series -/
def Subgroup.InAscendingNormalSeries (H : Subgroup G) (α : Ordinal)
    (S : AscendingNormalSeries G α) : Prop :=
  ∃ i : Ordinal, ∃ hi : i < α, S.series i hi = H

/-- An ascending normal series reaches G if the supremum of all members is ⊤ -/
def AscendingNormalSeries.ReachesTop (S : AscendingNormalSeries G α) : Prop :=
  ⨆ (i : Ordinal) (hi : i < α), S.series i hi = ⊤

/-- A group G is μ-overnilpotent if every cyclic subgroup of G is a member of
some ascending normal series of ordinal length less than μ that reaches G. -/
def IsOvernilpotent (G : Type*) [Group G] (μ : Cardinal) : Prop :=
  ∀ g : G, ∃ (α : Ordinal) (_ : α.card < μ) (S : AscendingNormalSeries G α),
    S.ReachesTop ∧ (Subgroup.zpowers g).InAscendingNormalSeries α S

/-- In radical class theory, a group is C-semisimple with respect to a class C
of groups if it has no nontrivial normal subgroups that belong to C.
Here, μ-semisimple means G has no nontrivial normal subgroup that is
μ-overnilpotent. -/
def IsSemisimpleOvernilpotent (G : Type*) [Group G] (μ : Cardinal) : Prop :=
  ∀ H : Subgroup G, H.Normal → H ≠ ⊥ →
    ¬ IsOvernilpotent H μ

/-- Kourovka Problem 3.43: For infinite cardinals μ₁ < μ₂, does there exist
a group G that is μ₂-overnilpotent and μ₁-semisimple? -/
theorem kourovka_3_43 :
    (∀ μ₁ μ₂ : Cardinal, Cardinal.aleph0 ≤ μ₁ → μ₁ < μ₂ →
      ∃ (G : Type*) (_ : Group G),
        IsOvernilpotent G μ₂ ∧ IsSemisimpleOvernilpotent G μ₁)
    ∨
    (∃ μ₁ μ₂ : Cardinal, Cardinal.aleph0 ≤ μ₁ ∧ μ₁ < μ₂ ∧
      ∀ (G : Type*) (_ : Group G),
        IsOvernilpotent G μ₂ → ¬ IsSemisimpleOvernilpotent G μ₁) := by
  sorry
