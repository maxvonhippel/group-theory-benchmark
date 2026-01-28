import Mathlib

/-!
# Problem 35: Estimating the Lp norm of self-convolution

Consider the class F of all integrable functions f : [0, 1] → ℝ≥0 with ∫ f = 1.
For 1 < p ≤ ∞, estimate cp := inf_{f∈F} ∥f ∗ f∥_p.

Known bounds mentioned in comments:
- c₂ ≥ 0.7559...
- c∞ ≥ 0.64
- c∞ ≤ 0.75049...
- c∞ ≥ c₂/2 (by Young's inequality)
-/

open MeasureTheory Set

noncomputable section

/-- The class F of nonnegative integrable functions on [0,1] with integral equal to 1 -/
def ClassF : Set ((Icc (0 : ℝ) 1) → ℝ) :=
  {f | (∀ x, 0 ≤ f x) ∧ Integrable f ∧ ∫ x, f x = 1}

/-- Self-convolution of a function defined on [0,1], extended to [0,2].
    For functions on [0,1], the convolution f * f is defined on [0,2] by
    (f * f)(t) = ∫₀¹ f(s) f(t-s) ds for s ∈ [0,1] and t-s ∈ [0,1]. -/
def selfConvolution (f : ℝ → ℝ) : ℝ → ℝ := fun t =>
  ∫ s in Icc 0 1, f s * f (t - s)

/-- The constant cp for exponent p, defined as the infimum of Lp norms of self-convolutions
    over functions in class F.

    For f : [0,1] → ℝ≥0 with ∫f = 1, we take the Lp norm of f*f over [0,2]. -/
def cp (p : ENNReal) : ENNReal :=
  sInf {norm_val : ENNReal |
    ∃ f : ℝ → ℝ,
      (∀ x, x ∈ Icc 0 1 → 0 ≤ f x) ∧
      (∀ x, x ∉ Icc 0 1 → f x = 0) ∧
      Integrable f ∧
      ∫ x in Icc 0 1, f x = 1 ∧
      norm_val = eLpNorm (selfConvolution f) p (volume.restrict (Icc 0 2))}

/-- The problem asks to estimate cp for 1 < p ≤ ∞. The comments provide known bounds:
    For p = 2: c₂ ≥ 0.7559
    For p = ∞: 0.64 ≤ c∞ ≤ 0.75049

    This theorem states the existence of bounds on cp. -/
theorem problem_35_estimate_cp (p : ENNReal) (hp : 1 < p) :
    ∃ (lower upper : ENNReal), lower ≤ cp p ∧ cp p ≤ upper := by
  sorry

/-- Known lower bound for p = 2: c₂ ≥ 0.7559 (from Green's first paper) -/
theorem c2_lower_bound : cp 2 ≥ 0.7559 := by
  sorry

/-- Known lower bound for p = ∞: c∞ ≥ 0.64 (Cloninger-Steinerberger) -/
theorem c_inf_lower_bound : cp ⊤ ≥ 0.64 := by
  sorry

/-- Known upper bound for p = ∞: c∞ ≤ 0.75049 (Matolcsi-Vinuesa) -/
theorem c_inf_upper_bound : cp ⊤ ≤ 0.75049 := by
  sorry

/-- Young's inequality implies c∞ ≥ c₂/2 -/
theorem young_inequality_bound : cp ⊤ ≥ cp 2 / 2 := by
  sorry

end
