import Mathlib

/-!
# Problem 22: Moreira's Theorem on Monochromatic x+y and xy

If {1, ..., N} is r-colored then, for N ≥ N₀(r), there are integers x, y ≥ 3
such that x + y, xy have the same color.

The problem asks to "find reasonable bounds for N₀(r)".

We formalize the existence statement (Moreira's theorem) as follows.
The actual question about finding "reasonable bounds" is a research question
that asks for explicit bounds, which we cannot formalize as a precise theorem
without specifying what bounds are claimed.

Moreira in fact proved the stronger result that x can also have the same color
as x + y and xy. This is also formalized below.

The comments also mention Hindman's famous question: can we find x, y, x + y, xy
all of the same color? This is formalized as an open conjecture.
-/

namespace Green22

/-- An r-coloring of {1, ..., N} is a function from {1, ..., N} to {0, ..., r-1}.
    We represent elements of {1, ..., N} as natural numbers with proofs. -/
def Coloring (N r : ℕ) := {n : ℕ // 1 ≤ n ∧ n ≤ N} → Fin r

/-- The property that x + y and xy have the same color in a given coloring.
    We require x, y ≥ 3, and x + y, xy must be in the range {1, ..., N}. -/
def hasMonochromaticSumProduct (N r : ℕ) (c : Coloring N r) : Prop :=
  ∃ (x y : ℕ) (_ : x ≥ 3) (_ : y ≥ 3)
    (hsum : 1 ≤ x + y ∧ x + y ≤ N)
    (hprod : 1 ≤ x * y ∧ x * y ≤ N),
    c ⟨x + y, hsum⟩ = c ⟨x * y, hprod⟩

/-- Moreira's theorem: For every r ≥ 1, there exists N₀ such that for all N ≥ N₀,
    any r-coloring of {1, ..., N} has x, y ≥ 3 with x+y and xy the same color. -/
theorem moreira_theorem (r : ℕ) (hr : r ≥ 1) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
      ∀ c : Coloring N r, hasMonochromaticSumProduct N r c := by
  sorry

/-- A bound function N₀ : ℕ → ℕ is valid if it satisfies Moreira's theorem -/
def IsValidBound (N₀ : ℕ → ℕ) : Prop :=
  ∀ r : ℕ, r ≥ 1 →
    ∀ N : ℕ, N ≥ N₀ r →
      ∀ c : Coloring N r, hasMonochromaticSumProduct N r c

/-- There exists a valid bound function (consequence of Moreira's theorem) -/
theorem exists_valid_bound : ∃ N₀ : ℕ → ℕ, IsValidBound N₀ := by
  sorry

/-- The stronger property: x, x + y, and xy all have the same color.
    This is what Moreira actually proved. -/
def hasMonochromaticTriple (N r : ℕ) (c : Coloring N r) : Prop :=
  ∃ (x y : ℕ) (_ : x ≥ 3) (_ : y ≥ 3)
    (hx : 1 ≤ x ∧ x ≤ N)
    (hsum : 1 ≤ x + y ∧ x + y ≤ N)
    (hprod : 1 ≤ x * y ∧ x * y ≤ N),
    c ⟨x, hx⟩ = c ⟨x + y, hsum⟩ ∧ c ⟨x, hx⟩ = c ⟨x * y, hprod⟩

/-- Moreira's stronger theorem: For every r ≥ 1, there exists N₀ such that
    for all N ≥ N₀, any r-coloring of {1, ..., N} has x, y ≥ 3 with
    x, x+y, and xy all the same color. -/
theorem moreira_stronger (r : ℕ) (hr : r ≥ 1) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
      ∀ c : Coloring N r, hasMonochromaticTriple N r c := by
  sorry

/-- The stronger result implies the original -/
theorem stronger_implies_original (N r : ℕ) (c : Coloring N r) :
    hasMonochromaticTriple N r c → hasMonochromaticSumProduct N r c := by
  intro ⟨x, y, hx3, hy3, hx, hsum, hprod, heq1, heq2⟩
  exact ⟨x, y, hx3, hy3, hsum, hprod, heq1.symm.trans heq2⟩

/-- Hindman's question (mentioned in comments): For every r ≥ 1, there exists N₀
    such that for all N ≥ N₀, any r-coloring of {1, ..., N} has x, y with
    x, y, x + y, and xy all the same color.

    This is the k = 2 case of Hindman's general question. -/
def hasHindmanQuadruple (N r : ℕ) (c : Coloring N r) : Prop :=
  ∃ (x y : ℕ) (_ : x ≥ 1) (_ : y ≥ 1) (_ : x ≠ y)
    (hx : 1 ≤ x ∧ x ≤ N)
    (hy : 1 ≤ y ∧ y ≤ N)
    (hsum : 1 ≤ x + y ∧ x + y ≤ N)
    (hprod : 1 ≤ x * y ∧ x * y ≤ N),
    c ⟨x, hx⟩ = c ⟨y, hy⟩ ∧
    c ⟨x, hx⟩ = c ⟨x + y, hsum⟩ ∧
    c ⟨x, hx⟩ = c ⟨x * y, hprod⟩

/-- Hindman's conjecture for k = 2 -/
def HindmanConjecture : Prop :=
  ∀ r : ℕ, r ≥ 1 →
    ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
      ∀ c : Coloring N r, hasHindmanQuadruple N r c

/-- The status of Hindman's conjecture is unknown -/
theorem hindman_conjecture_open : HindmanConjecture ∨ ¬HindmanConjecture := by
  sorry

end Green22
