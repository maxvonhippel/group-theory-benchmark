import Mathlib

/-!
# Problem 95 (Green's Problems)

**Problem Statement:**
Are a positive proportion of positive integers a sum of two palindromes?

**Update 2024:** D. Zakharov has shown that the answer is negative, showing that
the number of n ≤ X which are the sum of two base g palindromes is o(X).

We formalize this as: the natural density of positive integers that can be
expressed as a sum of two palindromes in base g ≥ 2 is zero.
-/

/-- The digits of a natural number n in base g, as a list (least significant first) -/
def digitsBase (g : ℕ) (n : ℕ) : List ℕ :=
  if h : g ≤ 1 then []
  else if hn : n = 0 then []
  else
    have : n / g < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by omega)
    (n % g) :: digitsBase g (n / g)
termination_by n

/-- A natural number is a palindrome in base g if its digit representation reads
    the same forwards and backwards. We also consider 0 to be a palindrome. -/
def isPalindrome (g : ℕ) (n : ℕ) : Prop :=
  g ≥ 2 → digitsBase g n = (digitsBase g n).reverse

/-- A natural number is a sum of two palindromes in base g -/
def isSumOfTwoPalindromes (g : ℕ) (n : ℕ) : Prop :=
  ∃ (a b : ℕ), isPalindrome g a ∧ isPalindrome g b ∧ n = a + b

/-- The set of positive integers ≤ X that are sums of two palindromes in base g -/
def sumOfTwoPalindromesUpTo (g : ℕ) (X : ℕ) : Set ℕ :=
  { n : ℕ | 1 ≤ n ∧ n ≤ X ∧ isSumOfTwoPalindromes g n }

/-- Counting function: number of positive integers ≤ X that are sums of two palindromes.
    This is defined using classical choice since isSumOfTwoPalindromes is not decidable. -/
noncomputable def countSumOfTwoPalindromes (g : ℕ) (X : ℕ) : ℕ :=
  Set.ncard { n : ℕ | 1 ≤ n ∧ n ≤ X ∧ isSumOfTwoPalindromes g n }

/--
**Zakharov's Theorem (2024):**
For any base g ≥ 2, the proportion of positive integers ≤ X that can be written
as a sum of two palindromes tends to 0 as X → ∞.

Formally: lim_{X → ∞} (countSumOfTwoPalindromes g X) / X = 0
-/
theorem zakharov_sum_of_two_palindromes (g : ℕ) (hg : g ≥ 2) :
    Filter.Tendsto (fun X : ℕ => (countSumOfTwoPalindromes g X : ℝ) / (X : ℝ))
      Filter.atTop (nhds 0) := by
  sorry

/--
Corollary: The answer to Problem 95 is negative.
A positive proportion of positive integers are NOT sums of two palindromes.
-/
theorem problem_95_negative (g : ℕ) (hg : g ≥ 2) :
    ¬ ∃ (c : ℝ), c > 0 ∧
      ∀ᶠ X in Filter.atTop,
        (countSumOfTwoPalindromes g X : ℝ) / (X : ℝ) ≥ c := by
  sorry
