import Mathlib

/-!
# Green Problem 18: Naive Corners in Finite Groups

**Problem Statement:**
Suppose that G is a finite group, and let A ⊂ G × G be a subset of density α.
Is it true that there are ≫_α |G|³ triples x, y, g such that (x, y), (gx, y), (x, gy)
all lie in A?

Such triples are called "naive corners" (terminology due to Tim Austin).

**Formalization:**
We formalize this as the existence of a function c : (0,1] → ℝ⁺ such that for any
finite group G and any subset A ⊆ G × G with density at least α, the number of
naive corner triples is at least c(α) · |G|³.
-/

open Finset

/-- A naive corner in G × G is a triple (x, y, g) where (x, y), (gx, y), and (x, gy)
    all lie in a given set A. -/
def IsNaiveCorner {G : Type*} [Group G] (A : Set (G × G)) (x y g : G) : Prop :=
  (x, y) ∈ A ∧ (g * x, y) ∈ A ∧ (x, g * y) ∈ A

/-- The set of naive corner triples for a set A ⊆ G × G -/
def naiveCornerTriples {G : Type*} [Group G] [DecidableEq G] [Fintype G]
    (A : Finset (G × G)) : Finset (G × G × G) :=
  (Finset.univ : Finset (G × G × G)).filter fun ⟨x, y, g⟩ =>
    (x, y) ∈ A ∧ (g * x, y) ∈ A ∧ (x, g * y) ∈ A

/-- The density of a subset A of G × G is |A| / |G|² -/
noncomputable def density {G : Type*} [Fintype G] (A : Finset (G × G)) : ℝ :=
  (A.card : ℝ) / ((Fintype.card G : ℝ) ^ 2)

/--
**Green Problem 18** (Tim Austin's Naive Corners Conjecture):

There exists a function c : ℝ → ℝ with c(α) > 0 for α > 0, such that
for any finite group G and any A ⊆ G × G with density ≥ α > 0,
the number of naive corner triples is at least c(α) · |G|³.

In big-O notation: #(naive corners) ≫_α |G|³
-/
theorem green_problem_18 :
    ∃ c : ℝ → ℝ, (∀ α > 0, c α > 0) ∧
      ∀ (G : Type*) [Group G] [DecidableEq G] [Fintype G] (A : Finset (G × G)),
        ∀ α > 0, density A ≥ α →
          ((naiveCornerTriples A).card : ℝ) ≥ c α * (Fintype.card G : ℝ) ^ 3 := by
  sorry

/--
A weaker version asking if at least one naive corner always exists when A has
positive density. This is also an open question (the problem asks for many corners).
-/
theorem green_problem_18_existence :
    ∀ (G : Type*) [Group G] [DecidableEq G] [Fintype G] (A : Finset (G × G)),
      A.Nonempty →
        ∃ x y g : G, IsNaiveCorner (A : Set (G × G)) x y g := by
  sorry
