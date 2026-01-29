/-
Kourovka Notebook Problem 7.27 (V. M. Levchuk)

Is it true that the group SL_n(q) contains, for sufficiently large q, a diagonal matrix
which is not contained in any proper irreducible subgroup of SL_n(q) with the exception
of block-monomial ones?

For n = 2, 3 the answer is known to be affirmative (V. M. Levchuk, in: Some problems of
the theory of groups and rings, Inst. of Physics SO AN SSSR, Krasnoyarsk, 1973 (Russian)).
Similar problems are interesting for other Chevalley groups.

DEFINITIONS:
- SL_n(q) is the special linear group of n×n matrices with determinant 1 over the finite
  field F_q.
- A subgroup H ≤ GL_n(F) is **irreducible** if its natural action on F^n has no proper
  nonzero invariant subspaces.
- A subgroup H ≤ GL_n(F) is **block-monomial** (with respect to some partition of
  {1,...,n}) if each matrix in H permutes the blocks and has nonzero entries only within
  those block positions. This generalizes monomial matrices.
- A diagonal matrix is one with M_ij = 0 for i ≠ j.
-/

import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.Fin.Basic

open Matrix

variable {n : ℕ} [NeZero n] {F : Type*} [Field F]

/--
A subgroup H of GL_n(F) **acts irreducibly** on F^n if the only H-invariant subspaces
are the trivial subspace {0} and the whole space F^n.
-/
def Subgroup.ActsIrreducibly (H : Subgroup (GeneralLinearGroup (Fin n) F)) : Prop :=
  ∀ (W : Submodule F (Fin n → F)),
    (∀ g : H, ∀ v : Fin n → F, v ∈ W →
      (g.val : Matrix (Fin n) (Fin n) F).mulVec v ∈ W) →
    W = ⊥ ∨ W = ⊤

/--
A subgroup H of GL_n(F) is **block-monomial** if it is contained in a subgroup that
permutes blocks and acts by scalar matrices within blocks (with respect to some
nontrivial partition of {1,...,n}).

For a precise definition, one would need to specify:
- A partition of Fin n into disjoint blocks B₁, B₂, ..., Bₖ
- Each matrix M in H permutes these blocks (i.e., for each block Bᵢ, there exists Bⱼ
  such that M maps Bᵢ into Bⱼ)
- The nonzero entries of M occur only within these block positions

This is a structural property related to reducibility over proper subspaces.
-/
def Subgroup.IsBlockMonomial (H : Subgroup (GeneralLinearGroup (Fin n) F)) : Prop :=
  -- A full definition would require specifying a block structure
  -- For formalization purposes, we leave this as an axiomatized predicate
  sorry

/-- A matrix M is diagonal if all off-diagonal entries are zero. -/
def Matrix.IsDiag {m : Type*} [DecidableEq m] (M : Matrix m m F) : Prop :=
  ∀ i j, i ≠ j → M i j = 0

/--
The natural embedding of SL_n(F) into GL_n(F).
-/
def SpecialLinearGroup.toGeneralLinear (n : Type*) [DecidableEq n] [Fintype n]
    (F : Type*) [CommRing F] : SpecialLinearGroup n F →* GeneralLinearGroup n F :=
  SpecialLinearGroup.toGL

/--
**Kourovka Problem 7.27** (V. M. Levchuk):

Is it true that for sufficiently large q, the group SL_n(F_q) contains a diagonal matrix
which is not contained in any proper irreducible subgroup of SL_n(F_q) with the exception
of block-monomial ones?

Formally: There exists a threshold q₀ such that for all prime powers q ≥ q₀, there exists
a diagonal matrix d ∈ SL_n(F_q) with the property that for any subgroup H of GL_n(F_q):
- If H is a proper subgroup (H ≠ GL_n(F_q))
- If H acts irreducibly on F_q^n
- If d ∈ H (viewing d as an element of GL_n via the natural embedding)
Then H must be block-monomial.

The conjecture is known to be true for n = 2 and n = 3 (by V. M. Levchuk, 1973).
-/
theorem kourovka_7_27 (n : ℕ) (hn : 2 ≤ n) :
    ∃ q₀ : ℕ, ∀ (p : ℕ) (k : ℕ) [hp : Fact (Nat.Prime p)] (hk : 0 < k),
      let q := p ^ k
      q₀ ≤ q →
      let F := GaloisField p k
      ∃ (d : SpecialLinearGroup (Fin n) F),
        -- d is a diagonal matrix
        (d : Matrix (Fin n) (Fin n) F).IsDiag ∧
        -- For any proper irreducible subgroup H containing d, H is block-monomial
        ∀ (H : Subgroup (GeneralLinearGroup (Fin n) F)),
          -- H is proper
          H < ⊤ →
          -- H acts irreducibly
          H.ActsIrreducibly →
          -- d is in H (via embedding SL_n → GL_n)
          (SpecialLinearGroup.toGeneralLinear (Fin n) F d : GeneralLinearGroup (Fin n) F) ∈ H →
          -- Then H is block-monomial
          H.IsBlockMonomial := by
  sorry

/-!
## Discussion

This problem concerns the structure of subgroups of finite special linear groups.
The key concepts are:

1. **Irreducible subgroups**: These are subgroups whose natural representation on
   the underlying vector space is irreducible (no proper invariant subspaces).

2. **Block-monomial subgroups**: These are subgroups with a specific structure where
   matrices permute certain blocks and have nonzero entries only in block positions.
   They are related to the concept of imprimitive linear groups.

3. **Diagonal matrices**: The conjecture asks for the existence of a "generic" diagonal
   matrix that avoids all exceptional proper irreducible subgroups except the block-monomial ones.

The result for n = 2, 3 was established by Levchuk in 1973. The general case remains
an open problem as of the time this problem was posed in the Kourovka Notebook.

This type of problem relates to the classification of maximal subgroups of classical groups,
an important topic in finite group theory with connections to the O'Nan-Scott theorem and
Aschbacher's theorem on subgroup structure of classical groups.
-/
