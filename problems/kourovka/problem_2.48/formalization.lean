/-
Kourovka Notebook Problem 2.48 (N. Aronszajn)

Let G be a connected topological group locally satisfying some identical relation
f|U = 1, where U is a neighborhood of the identity element of G.
Is it then true that f|G = 1?

An "identical relation" (or "law" or "identity") is a word in a free group that,
when interpreted in G, holds for all substitutions. For example:
- x^n = 1 (bounded exponent)
- [x,y] = 1 (commutativity / abelian)
- [[x,y],z] = 1 (nilpotent of class 2)

The problem asks: if such a law holds "locally" (for all substitutions from a
neighborhood of the identity), does it hold globally (for all substitutions from G)?
-/

import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.Topology.Connected.Basic

open Topology Set

/--
A group word is an element of the free group on n generators.
When we evaluate this word by substituting group elements for the generators,
we get an element of G.
-/
abbrev GroupWord (n : ℕ) := FreeGroup (Fin n)

/--
Given a group G and a function assigning elements of G to each generator,
we can evaluate a word in the free group to get an element of G.
This uses the universal property of free groups.
-/
noncomputable def evalWord {n : ℕ} {G : Type*} [Group G] (w : GroupWord n) (σ : Fin n → G) : G :=
  FreeGroup.lift σ w

/--
A word w is an "identical relation" (or "law") on a set S ⊆ G if
for every substitution σ : Fin n → S, the word evaluates to 1.
-/
def WordHoldsOn {n : ℕ} (G : Type*) [Group G] (w : GroupWord n) (S : Set G) : Prop :=
  ∀ σ : Fin n → G, (∀ i, σ i ∈ S) → evalWord w σ = 1

/--
A word is a law of the whole group if it holds for all substitutions.
-/
def IsGroupLaw {n : ℕ} (G : Type*) [Group G] (w : GroupWord n) : Prop :=
  ∀ σ : Fin n → G, evalWord w σ = 1

/--
Kourovka Problem 2.48 (N. Aronszajn):

Let G be a connected topological group. Suppose there exists a word w (an "identical
relation") and a neighborhood U of the identity such that w holds on U
(i.e., w evaluates to 1 for all substitutions from U).

Does w necessarily hold on all of G?

The statement below captures the question: is it true that for all connected
topological groups, local satisfaction of an identical relation implies global
satisfaction?
-/
theorem kourovka_2_48
    (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [ConnectedSpace G]
    (n : ℕ) (w : GroupWord n)
    (U : Set G) (hU_nhds : U ∈ nhds (1 : G))
    (hU_law : WordHoldsOn G w U) :
    IsGroupLaw G w := by
  sorry
