import Mathlib

/-!
# Problem 63: Hofstadter's Set and Positive Density

Let A be the smallest set containing 2 and 3 and such that a₁·a₂ - 1 ∈ A if a₁, a₂ ∈ A.
Does A have positive density?

Erdős [100] attributes this to Hofstadter. The answer is probably yes.

## Comments
A proof of this may have to involve some computation (as well as, presumably,
theoretical arguments) since the statement fails if a = 2 and b = 3 are replaced
by, say, a = 9 and b = 10, since the size of the 'words' of a given length
(for example, a(ab⁻¹)⁻¹ has length 3) grows much more quickly than the number of them.

We formalize this by defining:
1. An inductive set A as the smallest set containing 2 and 3 and closed under
   the operation (a₁, a₂) ↦ a₁ * a₂ - 1
2. Natural density (asymptotic density) of a set of natural numbers
3. The conjecture that A has positive natural density
-/

namespace Green63

/-- The set A is inductively defined as the smallest set containing 2 and 3
    and closed under the operation (a₁, a₂) ↦ a₁ * a₂ - 1 -/
inductive InHofstadterSet : ℕ → Prop where
  | base_two : InHofstadterSet 2
  | base_three : InHofstadterSet 3
  | closure : ∀ a₁ a₂, InHofstadterSet a₁ → InHofstadterSet a₂ →
      InHofstadterSet (a₁ * a₂ - 1)

/-- The Hofstadter set A as a set of natural numbers -/
def HofstadterSet : Set ℕ := {n | InHofstadterSet n}

/-- 2 is in the Hofstadter set -/
theorem two_mem : 2 ∈ HofstadterSet := InHofstadterSet.base_two

/-- 3 is in the Hofstadter set -/
theorem three_mem : 3 ∈ HofstadterSet := InHofstadterSet.base_three

/-- 5 = 2 * 3 - 1 is in the Hofstadter set -/
theorem five_mem : 5 ∈ HofstadterSet := by
  have h : 5 = 2 * 3 - 1 := rfl
  rw [h]
  exact InHofstadterSet.closure 2 3 InHofstadterSet.base_two InHofstadterSet.base_three

/-- The counting function for elements of a set up to n -/
noncomputable def countingFunction (S : Set ℕ) (n : ℕ) : ℕ :=
  Set.ncard (S ∩ Set.Iic n)

/-- The lower natural density of a set S ⊆ ℕ -/
noncomputable def lowerDensity (S : Set ℕ) : ℝ :=
  Filter.atTop.liminf (fun n : ℕ => (countingFunction S n : ℝ) / (n : ℝ))

/-- The upper natural density of a set S ⊆ ℕ -/
noncomputable def upperDensity (S : Set ℕ) : ℝ :=
  Filter.atTop.limsup (fun n : ℕ => (countingFunction S n : ℝ) / (n : ℝ))

/-- A set S ⊆ ℕ has positive lower natural density if
    liminf |S ∩ {0,...,n}| / n > 0 as n → ∞ -/
def hasPositiveLowerDensity (S : Set ℕ) : Prop :=
  0 < lowerDensity S

/-- A set S ⊆ ℕ has positive upper natural density if
    limsup |S ∩ {0,...,n}| / n > 0 as n → ∞ -/
def hasPositiveUpperDensity (S : Set ℕ) : Prop :=
  0 < upperDensity S

/-- Problem 63 Conjecture (Strong form): The Hofstadter set has positive lower density -/
theorem hofstadter_positive_lower_density : hasPositiveLowerDensity HofstadterSet := by
  sorry

/-- Problem 63 Conjecture (Weaker form): The Hofstadter set has positive upper density -/
theorem hofstadter_positive_upper_density : hasPositiveUpperDensity HofstadterSet := by
  sorry

/-!
## Counterexample: The set starting with 9 and 10

The problem comments mention that the analogous statement fails when 2 and 3 are
replaced by 9 and 10. We formalize this counterexample set.
-/

/-- The counterexample set starting with 9 and 10 -/
inductive InCounterexampleSet : ℕ → Prop where
  | base_nine : InCounterexampleSet 9
  | base_ten : InCounterexampleSet 10
  | closure : ∀ a₁ a₂, InCounterexampleSet a₁ → InCounterexampleSet a₂ →
      InCounterexampleSet (a₁ * a₂ - 1)

/-- The counterexample set B as a set of natural numbers -/
def CounterexampleSet : Set ℕ := {n | InCounterexampleSet n}

/-- The counterexample set does NOT have positive lower density -/
theorem counterexample_not_positive_density : ¬hasPositiveLowerDensity CounterexampleSet := by
  sorry

end Green63
