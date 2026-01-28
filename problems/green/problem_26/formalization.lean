/-
Problem 26. Let A1, . . . , A100 be 'cubes' in F_3^n, that is to say images of {0, 1}^n
under a linear automorphism of F_3^n. Is it true that A1 + · · · + A100 = F_3^n?

We formalize:
1. The vector space F_3^n (n-dimensional vector space over the field with 3 elements)
2. The standard cube {0,1}^n embedded in F_3^n
3. A "cube" as the image of {0,1}^n under a linear automorphism
4. The sumset of multiple sets
5. The conjecture that 100 cubes always sum to cover F_3^n
-/

import Mathlib

open scoped Pointwise

namespace Green26

variable (n : ℕ) [NeZero n]

/-- The field with 3 elements -/
abbrev F₃ := ZMod 3

/-- The vector space F_3^n -/
abbrev F₃n (n : ℕ) := Fin n → ZMod 3

/-- The standard cube {0,1}^n embedded in F_3^n -/
def standardCube (n : ℕ) : Set (F₃n n) :=
  {v | ∀ i, v i = 0 ∨ v i = 1}

/-- A "cube" in F_3^n is the image of the standard cube under a linear automorphism -/
def IsCube (A : Set (F₃n n)) : Prop :=
  ∃ φ : (F₃n n) ≃ₗ[F₃] (F₃n n), A = φ '' (standardCube n)

/-- The iterated sumset: A₁ + A₂ + ... + Aₖ -/
def iteratedSumset (sets : Fin k → Set (F₃n n)) : Set (F₃n n) :=
  {v | ∃ (f : Fin k → F₃n n), (∀ i, f i ∈ sets i) ∧ v = ∑ i, f i}

/-- The main conjecture: For any 100 cubes A₁, ..., A₁₀₀ in F_3^n,
    their sumset equals all of F_3^n -/
def Green26Conjecture : Prop :=
  ∀ (n : ℕ) [NeZero n], ∀ (cubes : Fin 100 → Set (F₃n n)),
    (∀ i, IsCube n (cubes i)) →
    iteratedSumset n cubes = Set.univ

/-- The problem asks whether this conjecture is true -/
theorem green_problem_26 : Green26Conjecture ∨ ¬Green26Conjecture := by
  sorry

/-- Alternative formulation: The minimum number of cubes needed to cover F_3^n
    is of interest. The problem essentially asks if 100 cubes always suffice. -/
noncomputable def minCubesForCoverage (n : ℕ) [NeZero n] : ℕ :=
  sInf {k | ∀ (cubes : Fin k → Set (F₃n n)),
    (∀ i, IsCube n (cubes i)) →
    iteratedSumset n cubes = Set.univ}

/-- A weaker form: For any n, there exists some number k such that k cubes suffice -/
theorem exists_coverage_number (n : ℕ) [NeZero n] :
    ∃ k, ∀ (cubes : Fin k → Set (F₃n n)),
      (∀ i, IsCube n (cubes i)) →
      iteratedSumset n cubes = Set.univ := by
  sorry

/-- The standard cube has cardinality 2^n -/
theorem standardCube_card (n : ℕ) [NeZero n] :
    (standardCube n).ncard = 2^n := by
  sorry

/-- The standard cube is finite -/
theorem standardCube_finite (n : ℕ) : (standardCube n).Finite := by
  sorry

/-- Any cube is finite (since it's the image of a finite set under a bijection) -/
theorem cube_finite (n : ℕ) (A : Set (F₃n n)) (hA : IsCube n A) : A.Finite := by
  sorry

end Green26
