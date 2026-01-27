/-
Kourovka Notebook Problem 1.40 (Sh. S. Kemkhadze)

Is a group a nilgroup if it is the product of two normal nilsubgroups?
By definition, a nilgroup is a group consisting of nilelements, in other words,
of (not necessarily boundedly) Engel elements.

Key Definitions:
- Engel element (nilelement): An element g ∈ G such that for every x ∈ G,
  there exists n (depending on x and g) with [x, g, g, ..., g] = 1
  (the iterated right commutator with n copies of g)
- Nilgroup: A group where every element is an Engel element
- Product of normal subgroups: G = HK where H, K ◁ G
-/

import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Algebra.Group.Commutator

/-! ## Iterated Right Commutators -/

/--
The iterated right commutator [x, g^{(n)}] defined recursively:
- [x, g^{(0)}] = x
- [x, g^{(n+1)}] = [[x, g^{(n)}], g]

This gives the n-fold iterated commutator [x, g, g, ..., g] with n copies of g.
-/
def iteratedRightCommutator {G : Type*} [Group G] (x g : G) : ℕ → G
  | 0 => x
  | n + 1 => ⁅iteratedRightCommutator x g n, g⁆

/-- Notation for iterated right commutator -/
notation:max "[" x ", " g "^(" n ")]" => iteratedRightCommutator x g n

/-! ## Engel Elements -/

/--
An element g of a group G is a **(right) Engel element** (also called a **nilelement**)
if for every x ∈ G, there exists a natural number n such that the iterated right
commutator [x, g, g, ..., g] (with n copies of g) equals the identity.

Note: The n may depend on both x and g; this is the "unbounded" Engel condition.
A bounded Engel element would require a uniform n working for all x.
-/
def IsEngelElement {G : Type*} [Group G] (g : G) : Prop :=
  ∀ x : G, ∃ n : ℕ, iteratedRightCommutator x g n = 1

/--
Alternative name: nilelement is the same as an Engel element.
-/
abbrev IsNilelement {G : Type*} [Group G] (g : G) : Prop := IsEngelElement g

/-! ## Nilgroups -/

/--
A **nilgroup** is a group in which every element is an Engel element (nilelement).

This is also known as an Engel group (though "Engel group" sometimes refers to
groups satisfying a bounded Engel condition).
-/
def IsNilgroup (G : Type*) [Group G] : Prop :=
  ∀ g : G, IsEngelElement g

/-! ## Nilsubgroups -/

/--
A subgroup H of G is a **nilsubgroup** if, when viewed as a group in its own right,
it is a nilgroup.
-/
def Subgroup.IsNilsubgroup {G : Type*} [Group G] (H : Subgroup G) : Prop :=
  IsNilgroup H

/-! ## Product of Subgroups -/

/--
A group G is the **internal product** of two subgroups H and K if every element
of G can be written as a product of an element of H and an element of K.

Formally: G = HK means {hk : h ∈ H, k ∈ K} = G.
-/
def IsProductOfSubgroups {G : Type*} [Group G] (H K : Subgroup G) : Prop :=
  ∀ g : G, ∃ h : H, ∃ k : K, g = h.val * k.val

/-! ## The Main Problem -/

/--
**Kourovka Notebook Problem 1.40** (Sh. S. Kemkhadze):

Is a group a nilgroup if it is the product of two normal nilsubgroups?

More precisely: If G = HK where H and K are normal subgroups and both H and K
are nilgroups (every element of H is an Engel element in H, and similarly for K),
does it follow that G is a nilgroup (every element of G is an Engel element in G)?

The question asks whether this implication holds.
-/
theorem kourovka_1_40 (G : Type*) [Group G]
    (H K : Subgroup G) [H.Normal] [K.Normal]
    (hH : H.IsNilsubgroup) (hK : K.IsNilsubgroup)
    (hProd : IsProductOfSubgroups H K) :
    IsNilgroup G := by
  sorry

/--
Alternative formulation: Does there exist a counterexample?

A counterexample would be a group G that is the product of two normal nilsubgroups
H and K, but G itself is not a nilgroup.
-/
def kourovka_1_40_counterexample_exists : Prop :=
  ∃ (G : Type) (_ : Group G) (H K : Subgroup G) (_ : H.Normal) (_ : K.Normal),
    H.IsNilsubgroup ∧ K.IsNilsubgroup ∧ IsProductOfSubgroups H K ∧ ¬IsNilgroup G

/-- The problem is equivalent to asking whether no counterexample exists -/
theorem kourovka_1_40_equiv_no_counterexample :
    (∀ (G : Type) [Group G] (H K : Subgroup G) [H.Normal] [K.Normal],
      H.IsNilsubgroup → K.IsNilsubgroup → IsProductOfSubgroups H K → IsNilgroup G) ↔
    ¬kourovka_1_40_counterexample_exists := by
  constructor
  · intro h ⟨G, hG, H, K, hHN, hKN, hH, hK, hProd, hNot⟩
    exact hNot (@h G hG H K hHN hKN hH hK hProd)
  · intro h G _ H K _ _ hH hK hProd
    by_contra hNot
    apply h
    exact ⟨G, inferInstance, H, K, inferInstance, inferInstance, hH, hK, hProd, hNot⟩

/-!
## Notes on the problem

### Key definitions

1. **Engel element (nilelement)**: An element g such that for all x, there exists n
   with [x, g, g, ..., g] = 1 (n-fold iterated commutator). The n may depend on x.

2. **Nilgroup**: A group where every element is an Engel element.

3. **Bounded vs. unbounded Engel condition**:
   - Bounded: There exists a fixed n that works for all pairs (x, g)
   - Unbounded (this problem): The n may depend on x and g

### The problem's subtlety

The key subtlety is that being an Engel element in a subgroup H does not
automatically make it an Engel element in the whole group G. When we compute
[x, g, g, ..., g] in G, the element x ranges over all of G, not just H.

So the question is whether the structure of G being a product of two normal
nilsubgroups is enough to guarantee that every element of G is an Engel element
when computed using all of G.

### Commutator convention

We use the convention [a, b] = a * b * a⁻¹ * b⁻¹ (which is Mathlib's convention
via `commutatorElement`). Some texts use the inverse convention [a, b] = a⁻¹ * b⁻¹ * a * b.
-/
