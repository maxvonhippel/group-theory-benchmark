/-
Problem 21. Rado's Boundedness Conjecture

Suppose that a₁, ..., aₖ are integers which do not satisfy Rado's condition:
thus if ∑_{i∈I} aᵢ = 0 then I = ∅. It then follows from Rado's theorem that
the equation a₁x₁ + ··· + aₖxₖ = 0 is not partition regular.

Write c(a₁, ..., aₖ) for the least number of colours required in order to
colour ℕ so that there is no monochromatic solution to a₁x₁ + ··· + aₖxₖ = 0.

Is c(a₁, ..., aₖ) bounded in terms of k only?

We formalize:
1. The "non-Rado condition": no non-empty subset of coefficients sums to zero
2. A coloring of ℕ⁺ using n colors
3. What it means to have no monochromatic solution
4. The minimum number of colors c(a₁, ..., aₖ)
5. Rado's boundedness conjecture: ∃ f : ℕ → ℕ such that c(a) ≤ f(k) for all valid a
-/

import Mathlib

open scoped BigOperators

namespace Green21

/-- A tuple of integers satisfies the "non-Rado condition" if no non-empty subset sums to zero.
    This is the negation of Rado's columns condition for a single equation. -/
def NonRadoCondition (a : Fin k → ℤ) : Prop :=
  ∀ I : Finset (Fin k), I.Nonempty → ∑ i ∈ I, a i ≠ 0

/-- A coloring of ℕ⁺ (positive naturals) with n colors -/
def Coloring (n : ℕ) := ℕ+ → Fin n

/-- A solution to a₁x₁ + ··· + aₖxₖ = 0 where all xᵢ are positive naturals -/
def IsSolution (a : Fin k → ℤ) (x : Fin k → ℕ+) : Prop :=
  ∑ i, a i * (x i : ℤ) = 0

/-- A coloring avoids monochromatic solutions if there is no solution where all xᵢ have the same color -/
def AvoidsMonochromatic (a : Fin k → ℤ) (χ : Coloring n) : Prop :=
  ∀ x : Fin k → ℕ+, IsSolution a x →
    ∃ i j : Fin k, χ (x i) ≠ χ (x j)

/-- An n-coloring exists that avoids monochromatic solutions -/
def HasAvoidingColoring (a : Fin k → ℤ) (n : ℕ) : Prop :=
  ∃ χ : Coloring n, AvoidsMonochromatic a χ

/-- c(a₁, ..., aₖ) is the minimum number of colors needed to avoid monochromatic solutions.
    We define it as the infimum of all n such that an n-coloring exists.
    Note: For coefficients satisfying the non-Rado condition, this is always finite by Rado's theorem. -/
noncomputable def radoNumber (a : Fin k → ℤ) : ℕ :=
  sInf {n : ℕ | n ≥ 1 ∧ HasAvoidingColoring a n}

/-- The set of valid coefficient tuples of length k (satisfying non-Rado condition) -/
def ValidCoefficients (k : ℕ) : Set (Fin k → ℤ) :=
  {a | NonRadoCondition a}

/-- Rado's Theorem implies that for coefficients satisfying the non-Rado condition,
    the equation is not partition regular, hence a finite coloring exists. -/
theorem rado_theorem_finite_coloring {k : ℕ} (a : Fin k → ℤ) (ha : NonRadoCondition a) :
    ∃ n : ℕ, n ≥ 1 ∧ HasAvoidingColoring a n := by
  sorry

/-- **Rado's Boundedness Conjecture** (Problem 21, Green):

For each k ∈ ℕ, there exists a constant f(k) such that for all tuples
(a₁, ..., aₖ) of integers satisfying the non-Rado condition,
we have c(a₁, ..., aₖ) ≤ f(k).

In other words, the minimum number of colors needed depends only on the
number of terms k, not on the specific coefficients. -/
theorem rados_boundedness_conjecture :
    ∀ k : ℕ, ∃ bound : ℕ, ∀ a : Fin k → ℤ,
      NonRadoCondition a → radoNumber a ≤ bound := by
  sorry

/-- Fox-Kleitman result: For k = 3, the bound is at most 24.
    That is, c(a₁, a₂, a₃) ≤ 24 for all valid triples. -/
theorem fox_kleitman_k3 :
    ∀ a : Fin 3 → ℤ, NonRadoCondition a → radoNumber a ≤ 24 := by
  sorry

/-
Additional formalization of the modular analogue mentioned in the problem:

Fox-Kleitman Conjecture 5: Let p be a prime, and suppose a₁, ..., aₖ are integers
with ∑_{i∈I} aᵢ ≢ 0 (mod p) for all non-empty I. Does there exist an f(k)-colouring
of (ℤ/pℤ)* with no monochromatic solution to a₁x₁ + ··· + aₖxₖ ≡ 0 (mod p)?
-/

/-- The modular non-Rado condition: no non-empty subset sums to 0 mod p -/
def ModularNonRadoCondition (p : ℕ) [Fact (Nat.Prime p)] (a : Fin k → ℤ) : Prop :=
  ∀ I : Finset (Fin k), I.Nonempty → (∑ i ∈ I, a i) % p ≠ 0

/-- A coloring of (ℤ/pℤ)* (nonzero elements mod p) -/
def ModularColoring (p n : ℕ) [Fact (Nat.Prime p)] := (ZMod p)ˣ → Fin n

/-- A solution mod p using nonzero elements -/
def IsModularSolution (p : ℕ) [Fact (Nat.Prime p)] (a : Fin k → ℤ) (x : Fin k → (ZMod p)ˣ) : Prop :=
  ∑ i, (a i : ZMod p) * (x i : ZMod p) = 0

/-- A modular coloring avoids monochromatic solutions -/
def ModularAvoidsMonochromatic (p : ℕ) [Fact (Nat.Prime p)] (a : Fin k → ℤ)
    (χ : ModularColoring p n) : Prop :=
  ∀ x : Fin k → (ZMod p)ˣ, IsModularSolution p a x →
    ∃ i j : Fin k, χ (x i) ≠ χ (x j)

/-- Fox-Kleitman Conjecture 5 (modular analogue of Rado's Boundedness Conjecture):
    For each k, there exists f(k) such that for any prime p and any tuple a
    satisfying the modular non-Rado condition, there is an f(k)-coloring of (ℤ/pℤ)*
    avoiding monochromatic solutions. -/
theorem modular_rados_boundedness_conjecture :
    ∀ k : ℕ, ∃ bound : ℕ, ∀ (p : ℕ) [hp : Fact (Nat.Prime p)] (a : Fin k → ℤ),
      ModularNonRadoCondition p a →
        ∃ χ : ModularColoring p bound, ModularAvoidsMonochromatic p a χ := by
  sorry

end Green21
