/-
Problem 12. Let G be an abelian group of size N, and suppose that A ⊂ G has density α.
Are there at least α^15 · N^10 tuples (x₁, ..., x₅, y₁, ..., y₅) ∈ G^10 such that
xᵢ + yⱼ ∈ A whenever j ∈ {i, i+1, i+2}?

Comments: This is very closely related to the Cayley graph case of simplest unknown
instance of Sidorenko's conjecture for graphs, that of the 'Möbius ladder' K₅,₅ \ C₁₀.

Interpretation: The condition "j ∈ {i, i+1, i+2}" with indices 1 to 5 is interpreted
cyclically (mod 5), yielding 15 constraints (matching K₅,₅ \ C₁₀ which has 15 edges).
The 15 pairs (i,j) are: (1,1), (1,2), (1,3), (2,2), (2,3), (2,4), (3,3), (3,4), (3,5),
(4,4), (4,5), (4,1), (5,5), (5,1), (5,2).
-/

import Mathlib

open scoped BigOperators

namespace Green12

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- The size of the finite abelian group G -/
noncomputable def groupSize (G : Type*) [Fintype G] : ℕ := Fintype.card G

/-- The density of a subset A of G is |A| / |G| -/
noncomputable def density (A : Finset G) : ℚ :=
  (A.card : ℚ) / (Fintype.card G : ℚ)

/-- Cyclic index: maps {0,1,2,3,4} to itself with wraparound -/
def cyclicSucc (i : Fin 5) (k : ℕ) : Fin 5 := ⟨(i.val + k) % 5, Nat.mod_lt _ (by omega)⟩

/-- The constraint: for index pair (i, j), we require xᵢ + yⱼ ∈ A
    The valid pairs (i, j) are those where j ∈ {i, i+1, i+2} (mod 5) -/
def validIndexPair (i j : Fin 5) : Bool :=
  j = i ∨ j = cyclicSucc i 1 ∨ j = cyclicSucc i 2

/-- A tuple (x, y) : (Fin 5 → G) × (Fin 5 → G) satisfies the Möbius constraint
    if xᵢ + yⱼ ∈ A for all valid index pairs (i, j) -/
def satisfiesMöbiusConstraint (A : Finset G) (x y : Fin 5 → G) : Prop :=
  ∀ i j : Fin 5, validIndexPair i j = true → x i + y j ∈ A

/-- Decidable instance for the constraint -/
instance (A : Finset G) (x y : Fin 5 → G) : Decidable (satisfiesMöbiusConstraint A x y) :=
  inferInstanceAs (Decidable (∀ i j : Fin 5, validIndexPair i j = true → x i + y j ∈ A))

/-- The set of all tuples (x, y) ∈ G^5 × G^5 satisfying the Möbius constraint -/
def möbiusTuples (A : Finset G) : Finset ((Fin 5 → G) × (Fin 5 → G)) :=
  Finset.univ.filter (fun p => satisfiesMöbiusConstraint A p.1 p.2)

/-- Count of Möbius tuples -/
noncomputable def möbiusTupleCount (A : Finset G) : ℕ := (möbiusTuples A).card

/-- The main conjecture: For any finite abelian group G and any subset A ⊆ G,
    the number of tuples (x₁,...,x₅,y₁,...,y₅) ∈ G^10 satisfying
    xᵢ + yⱼ ∈ A whenever j ∈ {i, i+1, i+2} (mod 5)
    is at least α^15 · N^10, where α = |A|/|G| and N = |G|.

    This is related to Sidorenko's conjecture for the Möbius ladder K₅,₅ \ C₁₀. -/
theorem green_problem_12 (A : Finset G) :
    (möbiusTupleCount A : ℚ) ≥
      (density A) ^ 15 * ((Fintype.card G : ℚ) ^ 10) := by
  sorry

/-- Equivalently, the normalized count is at least α^15 -/
theorem green_problem_12_normalized (A : Finset G) (hG : Fintype.card G > 0) :
    (möbiusTupleCount A : ℚ) / ((Fintype.card G : ℚ) ^ 10) ≥ (density A) ^ 15 := by
  sorry

/-- There are exactly 15 valid index pairs, matching the 15 edges of K₅,₅ \ C₁₀ -/
theorem validIndexPairs_count :
    (Finset.univ.filter (fun p : Fin 5 × Fin 5 => validIndexPair p.1 p.2 = true)).card = 15 := by
  native_decide

end Green12
