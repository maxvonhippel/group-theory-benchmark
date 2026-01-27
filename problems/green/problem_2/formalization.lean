import Mathlib

/-!
# Green Problem 2: Restricted Sumsets Avoiding a Set

**Problem Statement:**
Let A ⊂ ℤ be a set of n integers. Is there a set S ⊂ A of size (log n)^{100}
with S ˆ+ S disjoint from A?

Here S ˆ+ S denotes the restricted sumset {s₁ + s₂ : s₁, s₂ ∈ S, s₁ ≠ s₂}.

**Formalization Notes:**
This is an open problem asking whether the bound (log n)^100 is always achievable.
We formalize it as a statement that can be either true or false.
-/

/-- The restricted sumset S ˆ+ S consists of sums s₁ + s₂ where s₁, s₂ ∈ S and s₁ ≠ s₂ -/
def restrictedSumset (S : Finset ℤ) : Finset ℤ :=
  (S.product S).filter (fun p => p.1 ≠ p.2) |>.image (fun p => p.1 + p.2)

/--
Green Problem 2: For any finite set A of integers with n elements,
there exists a subset S ⊆ A with |S| ≥ ⌊(log n)^100⌋ such that
the restricted sumset S ˆ+ S is disjoint from A.

Note: This is an open problem. The statement may be true or false.
Current knowledge: Lower bound (log n)^{1+c} (Sanders), Upper bound e^{C√log n} (Ruzsa).
-/
theorem green_problem_2 :
    ∀ (A : Finset ℤ), A.card ≥ 2 →
    ∃ (S : Finset ℤ), S ⊆ A ∧
      S.card ≥ ⌊(Real.log A.card) ^ 100⌋₊ ∧
      Disjoint (restrictedSumset S) A := by
  sorry
