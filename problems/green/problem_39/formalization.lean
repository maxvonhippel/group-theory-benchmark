/-
Problem 39. If A ⊂ Z/pZ is random, |A| = √p, can we almost surely cover Z/pZ
with 100√p translates of A?

This is an OPEN QUESTION about random sets. We formalize the relevant definitions
and state the conjecture as a proposition.

Key concepts:
- A translate of A by t is the set {a + t : a ∈ A}
- Covering Z/pZ with k translates means ∃ t₁,...,t_k such that ⋃ᵢ (A + tᵢ) = Z/pZ
- "Random A with |A| = √p" means uniformly distributed over all subsets of size ⌊√p⌋
- "Almost surely" means probability → 1 as p → ∞

Note: The problem mentions "100√p" translates. Since √p ≤ |A| · √p would need to
cover p elements, we need roughly √p translates to have any chance of covering.
The factor 100 is asking if a linear factor suffices.
-/

import Mathlib

namespace Green39

open Finset BigOperators

/-- A translate of a set A by an element t in Z/pZ -/
def translate {p : ℕ} [NeZero p] (A : Finset (ZMod p)) (t : ZMod p) : Finset (ZMod p) :=
  A.image (· + t)

/-- A collection of translates (indexed by elements in T) covers Z/pZ -/
def translatesCovers {p : ℕ} [NeZero p] (A : Finset (ZMod p)) (T : Finset (ZMod p)) : Prop :=
  (T.biUnion (translate A)) = Finset.univ

/-- A set A can be covered using at most k translates -/
def canCoverWithTranslates {p : ℕ} [NeZero p] (A : Finset (ZMod p)) (k : ℕ) : Prop :=
  ∃ T : Finset (ZMod p), T.card ≤ k ∧ translatesCovers A T

/-- The set of all subsets of Z/pZ with a given cardinality -/
def subsetsOfSize (p : ℕ) [NeZero p] (k : ℕ) : Finset (Finset (ZMod p)) :=
  Finset.powersetCard k Finset.univ

/-- The number of subsets of size m that can be covered with at most k translates.
    We use Classical.dec to make the predicate decidable. -/
noncomputable def countCoverable (p : ℕ) [NeZero p] (m k : ℕ) : ℕ :=
  @Finset.card _ <| @Finset.filter _ (fun A => canCoverWithTranslates A k)
    (Classical.decPred _) (subsetsOfSize p m)

/-- The probability that a uniformly random subset of size m can be covered
    by at most k translates.

    This equals: |{A ⊆ Z/pZ : |A| = m ∧ A can be covered by k translates}| / C(p, m)
-/
noncomputable def probCoverable (p : ℕ) [NeZero p] (m k : ℕ) : ℚ :=
  if (subsetsOfSize p m).card = 0 then 0
  else (countCoverable p m k : ℚ) / ((subsetsOfSize p m).card : ℚ)

/-
The main open question (Green Problem 39):

For all ε > 0, there exists N such that for all primes p > N:
  If A is a uniformly random subset of Z/pZ with |A| = ⌊√p⌋,
  then P(A can be covered by 100⌊√p⌋ translates) ≥ 1 - ε.

This is the formal statement that the random covering succeeds "almost surely"
as p → ∞.
-/

/-- Green Problem 39: A random subset of Z/pZ of size √p can almost surely
    be covered by O(√p) translates.

    Formally: For all ε > 0, there exists N such that for all primes p > N,
    the probability that a random subset A of size ⌊√p⌋ can be covered by
    100⌊√p⌋ translates is at least 1 - ε.
-/
def greenProblem39 : Prop :=
  ∀ ε : ℚ, ε > 0 →
    ∃ N : ℕ, ∀ p : ℕ, (hp : Nat.Prime p) → p > N →
      haveI : NeZero p := ⟨Nat.Prime.ne_zero hp⟩
      probCoverable p (Nat.sqrt p) (100 * Nat.sqrt p) ≥ 1 - ε

/-
Note: The comments to the problem mention that even with the constant 100
replaced by 1.01, the answer is unknown. This suggests the problem is asking
whether ANY linear factor suffices.

A stronger (but still open) form of the question:
-/

/-- Stronger version: Does ANY constant factor work? -/
def greenProblem39Strong : Prop :=
  ∃ C : ℕ, C > 0 ∧
    ∀ ε : ℚ, ε > 0 →
      ∃ N : ℕ, ∀ p : ℕ, (hp : Nat.Prime p) → p > N →
        haveI : NeZero p := ⟨Nat.Prime.ne_zero hp⟩
        probCoverable p (Nat.sqrt p) (C * Nat.sqrt p) ≥ 1 - ε

end Green39
