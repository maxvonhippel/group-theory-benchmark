/-
Kourovka Problem 4.42

For what natural numbers n does the following equality hold:
  GL_n(ℝ) = D_n(ℝ) · O_n(ℝ) · UT_n(ℝ) · GL_n(ℤ)?

Where:
- GL_n(R) = general linear group (invertible n×n matrices over R)
- D_n(ℝ) = diagonal matrices with positive real diagonal entries
- O_n(ℝ) = orthogonal matrices
- UT_n(ℝ) = upper unitriangular matrices (upper triangular with 1s on diagonal)
- GL_n(ℤ) = integer matrices with determinant ±1

Known results:
- The equality holds for n ≤ 3 (Narzullayev)
- The equality does not hold for all sufficiently large n (Akhmedov)
- Status for n ≥ 6 was open at time of problem publication
-/

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Int.Basic

open Matrix

variable (n : ℕ) [NeZero n]

/-- A diagonal matrix with positive real diagonal entries -/
def PositiveDiagonalMatrix (n : ℕ) : Set (Matrix (Fin n) (Fin n) ℝ) :=
  {M | (∀ i j, i ≠ j → M i j = 0) ∧ (∀ i, M i i > 0)}

/-- The orthogonal group O_n(ℝ): matrices M such that M * Mᵀ = 1 -/
def OrthogonalMatrix (n : ℕ) : Set (Matrix (Fin n) (Fin n) ℝ) :=
  {M | M * Mᵀ = 1}

/-- Upper unitriangular matrices: upper triangular with 1s on the diagonal -/
def UpperUnitriangularMatrix (n : ℕ) : Set (Matrix (Fin n) (Fin n) ℝ) :=
  {M | (∀ i j, j < i → M i j = 0) ∧ (∀ i, M i i = 1)}

/-- Integer matrices embedded in real matrices -/
def IntegerMatrix (n : ℕ) : Set (Matrix (Fin n) (Fin n) ℝ) :=
  {M | ∀ i j, ∃ k : ℤ, M i j = k}

/-- GL_n(ℤ) embedded in real matrices: integer matrices with determinant ±1 -/
def IntegerInvertibleMatrix (n : ℕ) : Set (Matrix (Fin n) (Fin n) ℝ) :=
  {M | M ∈ IntegerMatrix n ∧ (M.det = 1 ∨ M.det = -1)}

/-- The set of invertible real n×n matrices -/
def InvertibleMatrix (n : ℕ) : Set (Matrix (Fin n) (Fin n) ℝ) :=
  {M | IsUnit M.det}

/-- The product set D_n(ℝ) · O_n(ℝ) · UT_n(ℝ) · GL_n(ℤ) -/
def DecompositionSet (n : ℕ) : Set (Matrix (Fin n) (Fin n) ℝ) :=
  {M | ∃ (D : Matrix (Fin n) (Fin n) ℝ) (O : Matrix (Fin n) (Fin n) ℝ)
         (U : Matrix (Fin n) (Fin n) ℝ) (Z : Matrix (Fin n) (Fin n) ℝ),
       D ∈ PositiveDiagonalMatrix n ∧
       O ∈ OrthogonalMatrix n ∧
       U ∈ UpperUnitriangularMatrix n ∧
       Z ∈ IntegerInvertibleMatrix n ∧
       M = D * O * U * Z}

/-- The decomposition property: whether GL_n(ℝ) = D_n(ℝ) · O_n(ℝ) · UT_n(ℝ) · GL_n(ℤ) -/
def HasMinkowskiDecomposition (n : ℕ) : Prop :=
  InvertibleMatrix n = DecompositionSet n

/-- Kourovka Problem 4.42: Characterize the natural numbers n for which
    GL_n(ℝ) = D_n(ℝ) · O_n(ℝ) · UT_n(ℝ) · GL_n(ℤ) holds.

    Known: holds for n ≤ 3, fails for sufficiently large n. -/
theorem kourovka_4_42 :
    ∃ S : Set ℕ, (∀ n, HasMinkowskiDecomposition n ↔ n ∈ S) ∧
    ({1, 2, 3} : Set ℕ) ⊆ S := by
  sorry

/-- The decomposition holds for n = 1 -/
theorem decomposition_holds_n1 : HasMinkowskiDecomposition 1 := by
  sorry

/-- The decomposition holds for n = 2 -/
theorem decomposition_holds_n2 : HasMinkowskiDecomposition 2 := by
  sorry

/-- The decomposition holds for n = 3 -/
theorem decomposition_holds_n3 : HasMinkowskiDecomposition 3 := by
  sorry

/-- There exists N such that for all n ≥ N, the decomposition fails -/
theorem decomposition_fails_large :
    ∃ N : ℕ, ∀ n ≥ N, ¬HasMinkowskiDecomposition n := by
  sorry
