/-
Problem 73. Let Γ be a smooth codimension 2 surface in ℝⁿ. Must Γ intersect
some 2-dimensional plane in 5 points, if n is sufficiently large?

Formalization approach:
- A "smooth codimension 2 surface in ℝⁿ" is the image of a smooth embedding
  from a smooth (n-2)-dimensional manifold into ℝⁿ.
- A "2-dimensional plane" is a 2-dimensional affine subspace of ℝⁿ.
- The question asks whether for sufficiently large n, the image must
  intersect some 2-plane in at least 5 points.
-/

import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Defs
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.EuclideanDist

open scoped Manifold
open Set

universe u

/-- A smooth embedding of an (n-2)-dimensional manifold into ℝⁿ -/
structure SmoothCodim2Surface (n : ℕ) : Type (u + 1) where
  /-- The source manifold (abstract smooth manifold of dimension n-2) -/
  M : Type u
  [topM : TopologicalSpace M]
  [chartedM : ChartedSpace (EuclideanSpace ℝ (Fin (n - 2))) M]
  [manifoldM : IsManifold (𝓡 (n - 2)) ⊤ M]
  /-- The embedding map -/
  embedding : M → EuclideanSpace ℝ (Fin n)
  /-- The embedding is smooth -/
  smooth : ContMDiff (𝓡 (n - 2)) (𝓡 n) ⊤ embedding
  /-- The embedding is injective -/
  injective : Function.Injective embedding

attribute [instance] SmoothCodim2Surface.topM SmoothCodim2Surface.chartedM SmoothCodim2Surface.manifoldM

/-- The image of the surface in ℝⁿ -/
def SmoothCodim2Surface.image {n : ℕ} (Γ : SmoothCodim2Surface.{u} n) : Set (EuclideanSpace ℝ (Fin n)) :=
  range Γ.embedding

/-- A 2-dimensional affine subspace of ℝⁿ -/
def IsTwoDimAffineSubspace {n : ℕ} (P : AffineSubspace ℝ (EuclideanSpace ℝ (Fin n))) : Prop :=
  Module.finrank ℝ P.direction = 2

/-- The intersection of a surface with an affine subspace has at least k points -/
def IntersectsInAtLeast {n : ℕ} (Γ : SmoothCodim2Surface.{u} n)
    (P : AffineSubspace ℝ (EuclideanSpace ℝ (Fin n))) (k : ℕ) : Prop :=
  ∃ S : Finset (EuclideanSpace ℝ (Fin n)),
    S.card ≥ k ∧ ↑S ⊆ Γ.image ∩ (P : Set (EuclideanSpace ℝ (Fin n)))

/--
Problem 73 Conjecture: For sufficiently large n, every smooth codimension 2
surface in ℝⁿ intersects some 2-dimensional plane in at least 5 points.
-/
def Green73 : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, n ≥ N → ∀ Γ : SmoothCodim2Surface.{0} n,
    ∃ P : AffineSubspace ℝ (EuclideanSpace ℝ (Fin n)),
      IsTwoDimAffineSubspace P ∧ IntersectsInAtLeast Γ P 5

/--
The generalized problem mentioned in comments: For a codimension d surface,
some d-dimensional plane intersects it in f(n,d) points.
-/
def Green73Generalized (f : ℕ → ℕ → ℕ) : Prop :=
  ∀ d : ℕ, ∃ N : ℕ, ∀ n : ℕ, n ≥ N → n ≥ d →
    ∀ (M : Type) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (n - d))) M]
      [IsManifold (𝓡 (n - d)) ⊤ M]
      (emb : M → EuclideanSpace ℝ (Fin n)),
      ContMDiff (𝓡 (n - d)) (𝓡 n) ⊤ emb →
      Function.Injective emb →
      ∃ P : AffineSubspace ℝ (EuclideanSpace ℝ (Fin n)),
        Module.finrank ℝ P.direction = d ∧
        ∃ S : Finset (EuclideanSpace ℝ (Fin n)),
          S.card ≥ f n d ∧ ↑S ⊆ range emb ∩ (P : Set (EuclideanSpace ℝ (Fin n)))
