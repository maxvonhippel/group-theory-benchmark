import Mathlib

/-!
# Green Problem 7: Ulam's Sequence Density

**Problem Statement:**
Define Ulam's sequence 1, 2, 3, 4, 6, 8, 11, 13, 16, 18, 26, 28, 36, ...
as follows: u₁ = 1, u₂ = 2, and u_{n+1} is the smallest number expressible as a sum
uᵢ + uⱼ, i < j ≤ n, in a unique way.

Does this sequence have positive density?

**Formalization Notes:**
We formalize the Ulam sequence and the question of whether it has positive
(lower) density. The second part of the problem about Fourier properties
is too vague for formal mathematical statement.

The sequence starts: 1, 2, 3, 4, 6, 8, 11, 13, 16, 18, 26, 28, 36, ...
Note: 5 = 1+4 = 2+3 (two ways), so 5 is excluded.
-/

open scoped Classical

/-- Number of pairs (i, j) with i < j ≤ n such that u(i) + u(j) = m -/
noncomputable def countUlamReps (u : ℕ → ℕ) (n m : ℕ) : ℕ :=
  Finset.card ((Finset.range n ×ˢ Finset.range n).filter fun p =>
    p.1 < p.2 ∧ u p.1 + u p.2 = m)

/-- m is uniquely representable as sum u(i) + u(j) with i < j < n -/
def isUniqueUlamRep (u : ℕ → ℕ) (n m : ℕ) : Prop :=
  ∃! p : ℕ × ℕ, p.1 < p.2 ∧ p.2 < n ∧ u p.1 + u p.2 = m

/-- Ulam sequence specification: u(n) is the n-th term (0-indexed: u(0)=1, u(1)=2) -/
structure IsUlamSequence (u : ℕ → ℕ) : Prop where
  base0 : u 0 = 1
  base1 : u 1 = 2
  strictly_increasing : StrictMono u
  unique_rep : ∀ n ≥ 2, isUniqueUlamRep u n (u n)
  minimal : ∀ n ≥ 2, ∀ m, u (n - 1) < m → m < u n → ¬isUniqueUlamRep u n m

/-- The Ulam sequence exists and is unique -/
theorem ulam_sequence_exists_unique : ∃! u : ℕ → ℕ, IsUlamSequence u := by
  sorry

/-- The canonical Ulam sequence -/
noncomputable def ulamSeq : ℕ → ℕ := Classical.choose ulam_sequence_exists_unique

/-- The set of values of the Ulam sequence -/
def UlamSet : Set ℕ := Set.range ulamSeq

/-- Counting function: number of elements of S in {0, 1, ..., n-1} -/
noncomputable def countingFn (S : Set ℕ) (n : ℕ) : ℕ :=
  Nat.card {x : ℕ | x < n ∧ x ∈ S}

/-- Lower density of a set S ⊆ ℕ -/
noncomputable def lowerDensity (S : Set ℕ) : ℝ :=
  Filter.liminf (fun n : ℕ => (countingFn S (n + 1) : ℝ) / (n + 1)) Filter.atTop

/-- Upper density of a set S ⊆ ℕ -/
noncomputable def upperDensity (S : Set ℕ) : ℝ :=
  Filter.limsup (fun n : ℕ => (countingFn S (n + 1) : ℝ) / (n + 1)) Filter.atTop

/-- Green Problem 7: Does the Ulam sequence have positive (lower) density?
    Computational evidence suggests density ≈ 0.07398... -/
theorem green_problem_7 : lowerDensity UlamSet > 0 := by
  sorry
