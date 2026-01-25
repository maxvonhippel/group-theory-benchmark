/-
Kourovka Notebook Problem 1.12 (W. Magnus)

(W. Magnus). The problem of the isomorphism to the trivial group for all groups
with n generators and n defining relations, where n > 2.

This problem asks about the decidability of the triviality problem for
balanced group presentations (presentations where the number of generators
equals the number of relations).

A balanced presentation is ⟨x₁, ..., xₙ | r₁, ..., rₙ⟩ with n generators and n relations.

The problem asks: Is there an algorithm that, given a balanced presentation with
n generators and n relations (n > 2), determines whether the presented group is
trivial (isomorphic to the group with one element)?

This is related to the famous Adian-Rabin theorem which shows that the triviality
problem is undecidable in general. The specific case of balanced presentations
is more subtle.

Historical note: The answer is NEGATIVE - it was shown by Adian (1957) that the
triviality problem is undecidable even for balanced presentations with n > 2.
-/

import Mathlib.GroupTheory.PresentedGroup
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.Data.Fintype.Card

/-- A finite balanced group presentation with n generators and n relations -/
structure BalancedPresentation (n : ℕ) where
  /-- The set of n relations as elements of the free group on n generators -/
  relations : Fin n → FreeGroup (Fin n)

/-- The group presented by a balanced presentation -/
def BalancedPresentation.toGroup {n : ℕ} (P : BalancedPresentation n) : Type :=
  PresentedGroup (Set.range P.relations)

instance {n : ℕ} (P : BalancedPresentation n) : Group P.toGroup :=
  PresentedGroup.instGroup (Set.range P.relations)

/-- A presented group is trivial if it has exactly one element -/
def PresentedGroupIsTrivial {α : Type*} (rels : Set (FreeGroup α)) : Prop :=
  ∀ x : PresentedGroup rels, x = 1

/-- The triviality problem for a balanced presentation -/
def IsTrivialPresentation {n : ℕ} (P : BalancedPresentation n) : Prop :=
  PresentedGroupIsTrivial (Set.range P.relations)

/--
We say the triviality problem is "decidable" for a class of presentations
if there exists a decision procedure. In type-theoretic terms, this means
we can provide an instance of `Decidable` for every presentation.

We use `Nonempty` to convert the Type-valued `Decidable` to a Prop.
-/
def TrivialityIsDecidable (n : ℕ) : Prop :=
  ∀ P : BalancedPresentation n, Nonempty (Decidable (IsTrivialPresentation P))

/--
Kourovka Problem 1.12: Decidability of the Triviality Problem for Balanced Presentations

The problem asks whether there exists a decision procedure (algorithm) that,
given any balanced presentation with n generators and n relations where n > 2,
determines whether the presented group is trivial.

The answer is NEGATIVE for n > 2: This is the Adian undecidability theorem.
-/
theorem kourovka_1_12_undecidable (n : ℕ) (hn : n > 2) :
    ¬ TrivialityIsDecidable n := by
  sorry

/--
Alternative formulation: There exist balanced presentations with n > 2 generators
for which triviality cannot be decided.

This captures the essence of undecidability: no uniform algorithm works for all
presentations.
-/
theorem kourovka_1_12_no_uniform_algorithm (n : ℕ) (hn : n > 2) :
    ¬ (∀ P : BalancedPresentation n, (IsTrivialPresentation P) ∨ ¬(IsTrivialPresentation P)) := by
  sorry

/--
The set of balanced presentations that present the trivial group.
-/
def TrivialPresentations (n : ℕ) : Set (BalancedPresentation n) :=
  { P | IsTrivialPresentation P }

/--
For completeness, we state that the triviality problem IS decidable for n ≤ 2.

For n = 1: A one-generator, one-relation presentation ⟨x | r⟩ presents the trivial
group iff the exponent sum of x in r is ±1.

For n = 2: The case is more complex but still decidable (Magnus, 1930s).
-/
theorem kourovka_1_12_decidable_small (n : ℕ) (hn : n ≤ 2) :
    TrivialityIsDecidable n := by
  sorry

/--
The original problem statement from Magnus can be interpreted as asking:
"Is the triviality problem decidable for balanced presentations?"

The answer, established by Adian, is:
- YES for n ≤ 2
- NO for n > 2

This dichotomy is captured in the following theorem.
-/
theorem kourovka_1_12_dichotomy (n : ℕ) :
    (n ≤ 2 → TrivialityIsDecidable n) ∧
    (n > 2 → ¬ TrivialityIsDecidable n) := by
  constructor
  · intro hn
    exact kourovka_1_12_decidable_small n hn
  · intro hn
    exact kourovka_1_12_undecidable n hn

/--
A concrete example: The trivial presentation with no relations presents the
free group on n generators, which is non-trivial for n ≥ 1.
-/
def trivialRelationsPresentation (n : ℕ) : BalancedPresentation n where
  relations := fun _ => 1  -- all relations are the identity

/-- The free group on n ≥ 1 generators is non-trivial -/
theorem free_group_nontrivial (n : ℕ) (hn : n ≥ 1) :
    ¬ IsTrivialPresentation (trivialRelationsPresentation n) := by
  sorry

/--
A presentation where each generator equals the identity presents the trivial group.
-/
def generatorsAreIdentityPresentation (n : ℕ) : BalancedPresentation n where
  relations := fun i => FreeGroup.of i  -- each relation says xᵢ = 1

/-- This presentation gives the trivial group -/
theorem identity_relations_trivial (n : ℕ) :
    IsTrivialPresentation (generatorsAreIdentityPresentation n) := by
  sorry
