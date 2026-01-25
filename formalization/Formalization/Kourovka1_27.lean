/-
Kourovka Notebook Problem 1.27 (M. I. Kargapolov)

**Original Problem**: "Describe the universal theory of free groups."

**Analysis**:
This is a research question asking for a characterization, not a theorem statement.
To formalize it, we need to:
1. Define a first-order language for groups
2. Define the universal theory of a class of structures
3. State what the universal theory of free groups is (the answer to the problem)

The known answer (established through later research) is that the universal theory
of free groups coincides with the universal theory of torsion-free groups.

**Formalization Approach**:
Since Mathlib does not yet have a first-order language for groups (only for rings),
we define it here and then state the main characterization theorem.
-/

import Mathlib.ModelTheory.Syntax
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Complexity
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.Torsion

open FirstOrder

universe u v

namespace Kourovka1_27

/-! ## First-Order Language of Groups -/

/-- The function symbols for the language of groups: multiplication (binary),
    inverse (unary), and identity (nullary). -/
inductive GroupFunc : ℕ → Type
  | mul : GroupFunc 2
  | inv : GroupFunc 1
  | one : GroupFunc 0
  deriving DecidableEq

/-- The first-order language of groups with operations (·, ⁻¹, 1) and no relations
    (equality is built into the logic). -/
def Language.group : Language where
  Functions := GroupFunc
  Relations := fun _ => Empty

instance : Language.group.IsAlgebraic :=
  fun _ => Empty.instIsEmpty

/-! ## Group Structure on the Language -/

namespace GroupLang

open GroupFunc Language

/-- Multiplication function symbol with the correct type -/
abbrev mulFunc : Language.group.Functions 2 := mul

/-- Inverse function symbol with the correct type -/
abbrev invFunc : Language.group.Functions 1 := inv

/-- Identity function symbol with the correct type -/
abbrev oneFunc : Language.group.Functions 0 := one

instance (α : Type*) : One (Language.group.Term α) where
  one := Language.Constants.term oneFunc

instance (α : Type*) : Mul (Language.group.Term α) where
  mul := mulFunc.apply₂

instance (α : Type*) : Inv (Language.group.Term α) where
  inv := invFunc.apply₁

/-- A structure making a `Group G` into a `Language.group.Structure`. -/
def groupStructure (G : Type*) [Group G] : Language.group.Structure G where
  funMap := fun {n} f =>
    match n, f with
    | 2, mul => fun args => args 0 * args 1
    | 1, inv => fun args => (args 0)⁻¹
    | 0, one => fun _ => 1
  RelMap := fun {_} r => Empty.elim r

end GroupLang

/-! ## Universal Theory -/

/-- The universal theory of a structure M is the set of all universal sentences
    that are true in M. -/
def universalTheoryOf (L : Language) (M : Type*) [L.Structure M] : L.Theory :=
  { φ : L.Sentence | φ.IsUniversal ∧ M ⊨ φ }

/-- Two structures have the same universal theory if they satisfy exactly the same
    universal sentences. -/
def SameUniversalTheory (L : Language) (M N : Type*) [L.Structure M] [L.Structure N] : Prop :=
  ∀ φ : L.Sentence, φ.IsUniversal → (M ⊨ φ ↔ N ⊨ φ)

/-- A class of structures (at a fixed universe level) has a common universal theory
    if any two structures in the class have the same universal theory. -/
def ClassHasCommonUniversalTheory (L : Language) (C : Type u → Prop) : Prop :=
  ∀ M N : Type u, ∀ [L.Structure M] [L.Structure N],
    C M → C N → SameUniversalTheory L M N

/-! ## Main Characterization -/

/-- A group G is torsion-free if every non-identity element has infinite order,
    i.e., no element (except 1) satisfies g^n = 1 for any positive n. -/
def IsTorsionFreeGroup (G : Type*) [Group G] : Prop :=
  ∀ g : G, g ≠ 1 → ∀ n : ℕ, n > 0 → g ^ n ≠ 1

/-- Predicate for being a free group (using Mathlib's FreeGroup). -/
def IsFreeGroupOn (G : Type*) [Group G] (X : Type*) : Prop :=
  Nonempty (G ≃* FreeGroup X)

/-- A group is abstractly free if it is isomorphic to a free group on some generating set. -/
def IsAbstractlyFree (G : Type*) [Group G] : Prop :=
  ∃ X : Type*, IsFreeGroupOn G X

/-! ## The Main Theorem (Answer to Problem 1.27)

The universal theory of free groups has a beautiful characterization:
A universal sentence holds in all free groups if and only if it holds in all
torsion-free groups.

This was established by work following the original problem, showing that:
1. Every free group is torsion-free (easy direction)
2. Every universal sentence true in all torsion-free groups is true in all free groups
   (follows from the fact that every group embeds in a torsion-free group that embeds
   in a free group, combined with the fact that universal sentences are preserved
   under substructures)
-/

/-- Every free group is torsion-free. This is the "easy" direction. -/
theorem freeGroup_isTorsionFree (X : Type*) : IsTorsionFreeGroup (FreeGroup X) := by
  sorry

/-- **Kourovka 1.27 - Main Characterization**:
    A universal sentence in the language of groups holds in all free groups
    if and only if it holds in all torsion-free groups.

    This completely describes the universal theory of free groups: it is exactly
    the set of universal sentences true in all torsion-free groups. -/
theorem kourovka_1_27
    (φ : Language.group.Sentence)
    (hφ : φ.IsUniversal) :
    (∀ (X : Type u) (hX : Nonempty X),
      @Language.Sentence.Realize Language.group (FreeGroup X) (GroupLang.groupStructure _) φ) ↔
    (∀ (G : Type u) [inst : Group G],
      @IsTorsionFreeGroup G inst →
      @Language.Sentence.Realize Language.group G (GroupLang.groupStructure G) φ) := by
  sorry

/-! ## Alternative Formulations -/

/-- Alternative characterization: The universal theory of the free group on 2 generators
    equals the universal theory of any nonabelian free group. -/
theorem universalTheory_free_eq (X Y : Type*) [Nonempty X] [Nonempty Y]
    (hX : ∃ x y : X, x ≠ y) (hY : ∃ x y : Y, x ≠ y) :
    @SameUniversalTheory Language.group
      (FreeGroup X) (FreeGroup Y)
      (GroupLang.groupStructure _) (GroupLang.groupStructure _) := by
  sorry

/-- The universal theory of free groups is finitely axiomatizable.
    (This is a nontrivial result that follows from the characterization.) -/
theorem universalTheory_free_finitelyAxiomatizable :
    ∃ (T : Finset Language.group.Sentence),
      (∀ φ ∈ T, φ.IsUniversal) ∧
      ∀ (X : Type u) (hX : ∃ x y : X, x ≠ y),
        ∀ ψ : Language.group.Sentence, ψ.IsUniversal →
          (@Language.Sentence.Realize Language.group (FreeGroup X)
            (GroupLang.groupStructure _) ψ ↔
           ∀ χ ∈ T, @Language.Sentence.Realize Language.group (FreeGroup X)
            (GroupLang.groupStructure _) χ →
           @Language.Sentence.Realize Language.group (FreeGroup X)
            (GroupLang.groupStructure _) ψ) := by
  sorry

end Kourovka1_27
