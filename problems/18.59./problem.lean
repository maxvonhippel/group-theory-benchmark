/-
Kourovka Notebook Problem 18.59

Problem Statement:
Does there exist a periodic group G such that:
1. G contains an involution
2. All involutions in G are conjugate
3. The centralizer of every involution i is isomorphic to ⟨i⟩ × L₂(P),
   where P is some infinite locally finite field of characteristic 2?

Posed by: D. V. Lytkina

Mathematical Context:
- L₂(P) = PSL(2, P) is the projective special linear group over field P
- A locally finite field of characteristic 2 is a union of finite fields GF(2^n)
- The algebraic closure of GF(2) is such a field
- A periodic group (also called torsion group) is one where every element has finite order
- An involution is an element of order 2

Investigation Summary (via GAP computations):
1. In PSL(2, 2^n), all involutions are conjugate (single conjugacy class)
2. The centralizer of an involution in PSL(2, 2^n) is elementary abelian of order 2^n
3. This centralizer structure is (C₂)^n, NOT ⟨i⟩ × PSL(2, F)
4. No finite simple group has the required centralizer structure
5. The problem specifically asks about INFINITE locally finite groups

Why this problem is hard:
- It requires constructing an infinite group with very specific properties
- Finite approximations don't help: no finite group has this centralizer structure
- The centralizer ⟨i⟩ × L₂(P) would be non-solvable (since L₂(P) is simple)
- But in known simple groups, involution centralizers don't have this form

Status: OPEN PROBLEM - Neither proved nor disproved
-/

universe u v

-- Basic group structure without notation conflicts
structure GroupData (G : Type u) where
  mul : G → G → G
  one : G
  inv : G → G
  mul_assoc : ∀ a b c : G, mul (mul a b) c = mul a (mul b c)
  one_mul : ∀ a : G, mul one a = a
  mul_one : ∀ a : G, mul a one = a
  inv_mul_cancel : ∀ a : G, mul (inv a) a = one
  mul_inv_cancel : ∀ a : G, mul a (inv a) = one

-- Power function: g^n
def gpow {G : Type u} (grp : GroupData G) (g : G) : Nat → G
  | 0 => grp.one
  | n + 1 => grp.mul g (gpow grp g n)

-- An element g has finite order if g^n = 1 for some positive n
def HasFiniteOrder {G : Type u} (grp : GroupData G) (g : G) : Prop :=
  ∃ n : Nat, n > 0 ∧ gpow grp g n = grp.one

-- A group is periodic if every element has finite order
def IsPeriodic {G : Type u} (grp : GroupData G) : Prop :=
  ∀ g : G, HasFiniteOrder grp g

-- An involution is an element of order 2
def IsInvolution {G : Type u} (grp : GroupData G) (g : G) : Prop :=
  g ≠ grp.one ∧ grp.mul g g = grp.one

-- Two elements are conjugate
def AreConjugate {G : Type u} (grp : GroupData G) (a b : G) : Prop :=
  ∃ g : G, b = grp.mul (grp.inv g) (grp.mul a g)

-- All involutions are conjugate
def AllInvolutionsConjugate {G : Type u} (grp : GroupData G) : Prop :=
  ∀ i j : G, IsInvolution grp i → IsInvolution grp j → AreConjugate grp i j

-- Centralizer of an element (as a predicate)
def InCentralizer {G : Type u} (grp : GroupData G) (a : G) (g : G) : Prop :=
  grp.mul g a = grp.mul a g

-- Placeholder for PSL(2, F) - the projective special linear group
-- Full definition requires field theory and matrix groups
axiom PSL2 : Type v → Type v
axiom PSL2_group : (F : Type v) → GroupData (PSL2 F)

-- Placeholder for infinite locally finite field of characteristic 2
-- This is the algebraic closure of GF(2), or equivalently the union of all GF(2^n)
axiom LocallyFiniteField2 : Type v
axiom LocallyFiniteField2_infinite : ∀ n : Nat, ∃ f : Fin n → LocallyFiniteField2, Function.Injective f
axiom LocallyFiniteField2_char2 : True  -- Characteristic 2 property (placeholder)

-- Direct product structure
structure DirectProduct (A B : Type u) where
  fst : A
  snd : B

def directProductGroup {A B : Type u} (grpA : GroupData A) (grpB : GroupData B) : GroupData (DirectProduct A B) where
  mul := fun x y => ⟨grpA.mul x.fst y.fst, grpB.mul x.snd y.snd⟩
  one := ⟨grpA.one, grpB.one⟩
  inv := fun x => ⟨grpA.inv x.fst, grpB.inv x.snd⟩
  mul_assoc := fun a b c => by simp [grpA.mul_assoc, grpB.mul_assoc]
  one_mul := fun a => by simp [grpA.one_mul, grpB.one_mul]
  mul_one := fun a => by simp [grpA.mul_one, grpB.mul_one]
  inv_mul_cancel := fun a => by simp [grpA.inv_mul_cancel, grpB.inv_mul_cancel]
  mul_inv_cancel := fun a => by simp [grpA.mul_inv_cancel, grpB.mul_inv_cancel]

-- Cyclic group of order 2
inductive C2 : Type where
  | e : C2  -- identity
  | g : C2  -- generator (the involution)

def C2_group : GroupData C2 where
  mul := fun x y => match x, y with
    | C2.e, z => z
    | z, C2.e => z
    | C2.g, C2.g => C2.e
  one := C2.e
  inv := fun x => x  -- every element is its own inverse in C2
  mul_assoc := fun a b c => by cases a <;> cases b <;> cases c <;> rfl
  one_mul := fun a => by cases a <;> rfl
  mul_one := fun a => by cases a <;> rfl
  inv_mul_cancel := fun a => by cases a <;> rfl
  mul_inv_cancel := fun a => by cases a <;> rfl

-- Group isomorphism (simplified definition)
def GroupIso {G H : Type u} (grpG : GroupData G) (grpH : GroupData H) : Prop :=
  ∃ (f : G → H) (g : H → G),
    (∀ x, g (f x) = x) ∧
    (∀ y, f (g y) = y) ∧
    (∀ a b, f (grpG.mul a b) = grpH.mul (f a) (f b))

-- The centralizer structure required by the problem:
-- For every involution i in G, the centralizer C_G(i) ≅ ⟨i⟩ × L₂(P)
-- where ⟨i⟩ is the cyclic group generated by i (which is C2 since i is an involution)
def HasRequiredCentralizerStructure {G : Type u} (grp : GroupData G) (P : Type v) : Prop :=
  ∀ i : G, IsInvolution grp i →
    -- The centralizer of i should be isomorphic to C2 × PSL(2, P)
    -- This requires defining the centralizer as a subgroup and showing the isomorphism
    -- We leave this as sorry since the full construction requires significant infrastructure
    sorry

/-
Main Problem Statement (Kourovka 18.59)

The problem asks: Does such a group G exist?
We formalize this as an excluded middle statement, since the answer is unknown.
-/
theorem kourovka_18_59 :
  (∃ (G : Type u) (grp : GroupData G),
    -- G is periodic (every element has finite order)
    IsPeriodic grp ∧
    -- G contains at least one involution
    (∃ i : G, IsInvolution grp i) ∧
    -- All involutions in G are conjugate (single conjugacy class)
    AllInvolutionsConjugate grp ∧
    -- The centralizer of every involution has the form ⟨i⟩ × L₂(P)
    -- where P is an infinite locally finite field of characteristic 2
    HasRequiredCentralizerStructure grp LocallyFiniteField2)
  ∨
  ¬(∃ (G : Type u) (grp : GroupData G),
    IsPeriodic grp ∧
    (∃ i : G, IsInvolution grp i) ∧
    AllInvolutionsConjugate grp ∧
    HasRequiredCentralizerStructure grp LocallyFiniteField2)
  := by
  -- OPEN PROBLEM: We don't know which disjunct holds
  -- This problem was posed by D. V. Lytkina in the Kourovka Notebook (edition 18)
  --
  -- Computational evidence from GAP:
  -- - PSL(2, 4) ≅ A₅: centralizer of involution is C₂ × C₂ (order 4)
  -- - PSL(2, 8): centralizer of involution is C₂ × C₂ × C₂ (order 8)
  -- - PSL(2, 16): centralizer of involution is (C₂)⁴ (order 16)
  -- - PSL(3, 4): centralizer of involution is solvable of order 64
  -- - Suzuki groups Sz(q): centralizer has different structure
  --
  -- None of these have the required form ⟨i⟩ × L₂(P).
  -- The problem requires an infinite construction that may or may not exist.
  sorry

#check kourovka_18_59
