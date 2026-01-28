import Mathlib

/-!
# Green's Problem 93: Random Polynomials and Irreducibility

Problem 93: Is a random polynomial with coefficients in {0, 1} and nonzero constant
term almost surely irreducible?

## Mathematical Interpretation

A polynomial with coefficients in {0, 1} and nonzero constant term means the constant
term is 1 (since it must be 0 or 1, and nonzero means 1).

"Random polynomial" means we consider the uniform distribution over polynomials of
a given degree n with coefficients in {0, 1} and constant term 1.

"Almost surely" in this context means "with probability tending to 1 as n → ∞".

For monic degree n polynomials with coefficients in {0,1}: the constant term is fixed
at 1, the leading coefficient is 1, and we choose the remaining n-1 coefficients
uniformly from {0, 1}. There are 2^(n-1) such polynomials for n ≥ 1.

The question is: what is the limiting probability that such a polynomial is irreducible
over ℤ as the degree n → ∞?
-/

namespace Green93

open Polynomial Filter Classical

/-- A polynomial has coefficients in {0, 1} if all coefficients are 0 or 1 -/
def HasCoeffsIn01 (p : Polynomial ℤ) : Prop :=
  ∀ n : ℕ, p.coeff n = 0 ∨ p.coeff n = 1

/-- A polynomial has nonzero constant term -/
def HasNonzeroConstant (p : Polynomial ℤ) : Prop :=
  p.coeff 0 = 1

/-- The set of monic polynomials of degree exactly n with coefficients in {0,1}
    and constant term 1 -/
def PolysWithCoeffs01Degree (n : ℕ) : Set (Polynomial ℤ) :=
  {p | HasCoeffsIn01 p ∧ HasNonzeroConstant p ∧ p.natDegree = n ∧ p.Monic}

/-- Build a monic polynomial of degree (n+1) with coefficients in {0,1} and constant term 1,
    where the intermediate coefficients are given by the function `coeffs`.
    Specifically, builds: 1 + Σᵢ (coeffs i) * X^(i+1) + X^(n+1) -/
noncomputable def buildPoly (n : ℕ) (coeffs : Fin n → Fin 2) : Polynomial ℤ :=
  1 + (Finset.univ.sum fun i : Fin n =>
    Polynomial.C ((coeffs i).val : ℤ) * Polynomial.X ^ (i.val + 1)) +
  Polynomial.X ^ (n + 1)

/-- The finite set of monic polynomials of degree (n+1) with coefficients in {0,1}
    and constant term 1, represented explicitly as a Finset.
    For degree (n+1), we choose n coefficients (for X¹, X², ..., Xⁿ) freely from {0, 1}. -/
noncomputable def BinaryPolynomialsOfDegree (n : ℕ) : Finset (Polynomial ℤ) :=
  Finset.univ.image (buildPoly n)

/-- The count of monic polynomials of degree n with coefficients in {0,1} and constant term 1.
    For n = 0, there is 1 such polynomial (the constant 1).
    For n ≥ 1, there are 2^(n-1) such polynomials (constant term = 1, leading coeff = 1,
    middle n-1 coefficients are free). -/
def NumPolysWithCoeffs01Degree (n : ℕ) : ℕ :=
  if n = 0 then 1 else 2^(n-1)

/-- The number of irreducible polynomials in BinaryPolynomialsOfDegree n -/
noncomputable def NumIrreduciblePolysOfDegree (n : ℕ) : ℕ :=
  @Finset.card _ <| @Finset.filter _ (fun p => Irreducible p)
    (Classical.decPred _) (BinaryPolynomialsOfDegree n)

/-- The proportion of irreducible polynomials among monic polynomials of degree (n+1)
    with coefficients in {0,1} and constant term 1 -/
noncomputable def ProportionIrreducible (n : ℕ) : ℝ :=
  if (BinaryPolynomialsOfDegree n).card = 0 then 0
  else (NumIrreduciblePolysOfDegree n : ℝ) / ((BinaryPolynomialsOfDegree n).card : ℝ)

/-- Problem 93: Does the probability of irreducibility tend to 1 as degree tends to ∞?

    This asks whether a random polynomial with {0,1} coefficients and nonzero constant
    term is "almost surely" irreducible, meaning the proportion of irreducible ones
    approaches 1 as the degree grows. -/
def GreenProblem93 : Prop :=
  Tendsto ProportionIrreducible atTop (nhds 1)

/-- The main theorem statement (open problem).
    The actual conjecture is that GreenProblem93 holds, i.e., the proportion
    of irreducible polynomials tends to 1 as degree tends to ∞. -/
theorem green_problem_93 : GreenProblem93 := by
  sorry

end Green93
