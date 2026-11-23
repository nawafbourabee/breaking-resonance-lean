import BreakingResonance.BoundedDurationBounds
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Analysis.SpecificLimits.Normed

/-! The geometric law of the floor of an exponential duration, and its
characteristic function after the Bernoulli draw. -/
noncomputable section
namespace BreakingResonance
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

theorem exponentialDuration_Iic {s : ℝ} (hs : 0 < s) {t : ℝ} (ht : 0 ≤ t) :
    (expMeasure s).real (Iic t) = 1 - Real.exp (-(s*t)) := by
  let : IsProbabilityMeasure (expMeasure s) := isProbabilityMeasure_expMeasure hs
  rw [← cdf_eq_real, cdf_expMeasure_eq hs]
  simp [ht]

theorem exponentialDuration_positive {s : ℝ} (hs : 0 < s) :
    ∀ᵐ τ ∂expMeasure s, 0 < τ := by
  let : IsProbabilityMeasure (expMeasure s) := isProbabilityMeasure_expMeasure hs
  have hzero := exponentialDuration_Iic hs (t := 0) le_rfl
  simp only [mul_zero, neg_zero, Real.exp_zero, sub_self, Measure.real] at hzero
  rw [ae_iff]
  change expMeasure s {τ | ¬ 0 < τ} = 0
  simp only [not_lt]
  exact ((ENNReal.toReal_eq_zero_iff _).mp hzero).resolve_right (measure_ne_top _ _)

theorem exponentialDuration_interval {s a b : ℝ} (hs : 0 < s) (ha : 0 ≤ a) (hab : a ≤ b) :
    (expMeasure s).real (Ico a b) = Real.exp (-(s*a)) - Real.exp (-(s*b)) := by
  let : IsProbabilityMeasure (expMeasure s) := isProbabilityMeasure_expMeasure hs
  let : NullSingletonClass (expMeasure s) := by
    unfold expMeasure gammaMeasure
    infer_instance
  have hset : Iic b \ Iic a = Ioc a b := Iic_sdiff_Iic
  rw [Measure.real, measure_congr (Ico_ae_eq_Ioc (μ := expMeasure s)), ← Measure.real,
    ← hset, measureReal_sdiff (Iic_subset_Iic.mpr hab) measurableSet_Iic,
    exponentialDuration_Iic hs (ha.trans hab), exponentialDuration_Iic hs ha]
  ring

theorem exponentialDuration_floorMass {s h : ℝ} (hs : 0 < s) (hh : 0 < h) (j : ℕ) :
    let r := Real.exp (-(s*h))
    countLawWeight ((expMeasure s).map (fun τ => Nat.floor (τ/h))) j = (1-r)*r^j := by
  dsimp only
  rw [countLawWeight, floorDuration_map_apply_singleton h hh
    ((exponentialDuration_positive hs).mono fun _ ht => ht.le)]
  change (expMeasure s).real (Ico ((j : ℝ)*h) (((j : ℝ)+1)*h)) = _
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  rw [exponentialDuration_interval hs (mul_nonneg hj hh.le)
    (mul_le_mul_of_nonneg_right (by linarith) hh.le)]
  rw [show -(s*((j : ℝ)*h)) = (j : ℝ)*(-(s*h)) by ring,
    show -(s*(((j : ℝ)+1)*h)) = (j : ℝ)*(-(s*h)) + (-(s*h)) by ring,
    Real.exp_add, Real.exp_nat_mul]
  ring

/-- The floor of an exponential duration contributes a geometric series. -/
theorem exponentialDuration_floor_characteristic {s h : ℝ} (hs : 0 < s) (hh : 0 < h) (θ : ℝ) :
    let r := Real.exp (-(s*h))
    let z := Complex.exp ((θ : ℂ)*Complex.I)
    (∫ τ : ℝ, Complex.exp ((((Nat.floor (τ/h) : ℝ)*θ : ℝ) : ℂ)*Complex.I) ∂expMeasure s) =
      (1 - (r : ℂ)) / (1 - (r : ℂ)*z) := by
  dsimp only
  let r := Real.exp (-(s*h))
  let z := Complex.exp ((θ : ℂ)*Complex.I)
  let ρ := expMeasure s
  let : IsProbabilityMeasure ρ := isProbabilityMeasure_expMeasure hs
  let f (j : ℕ) := Complex.exp ((((j : ℝ)*θ : ℝ) : ℂ)*Complex.I)
  let q := ρ.map (fun τ => Nat.floor (τ/h))
  let : IsProbabilityMeasure q := Measure.isProbabilityMeasure_map (measurable_floorDuration h).aemeasurable
  have hfm : Measurable f := measurable_of_countable _
  have hfi : Integrable f q := Integrable.of_bound hfm.aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun _ => (Complex.norm_exp_ofReal_mul_I _).le)
  have hr : 0 < r := Real.exp_pos _
  have hr₁ : r < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr (mul_pos hs hh))
  have hnorm : ‖(r : ℂ)*z‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr.le,
      show ‖z‖ = 1 from Complex.norm_exp_ofReal_mul_I θ, mul_one]
    exact hr₁
  change (∫ τ, f (Nat.floor (τ/h)) ∂ρ) = _
  rw [← integral_map (measurable_floorDuration h).aemeasurable hfm.aestronglyMeasurable,
    integral_countable hfi]
  have he (j : ℕ) : (q.real {j}) • f j = (1 - (r : ℂ))*((r : ℂ)*z)^j := by
    change (countLawWeight q j : ℂ) * f j = _
    rw [exponentialDuration_floorMass hs hh]
    change (((1-r)*r^j : ℝ) : ℂ) * f j = _
    have hpow : f j = z^j := by
      dsimp only [f, z]
      rw [← Complex.exp_nat_mul]
      push_cast
      ring_nf
    rw [hpow]
    push_cast only [Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_pow]
    rw [mul_pow]
    ring
  simp_rw [he]
  rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hnorm, div_eq_mul_inv]

/-- The full exponential law in Appendix C, with the same Bernoulli factor
as the bounded laws. -/
theorem exponentialDuration_rounded_characteristic {s h : ℝ}
    (hs : 0 < s) (hh : 0 < h) (θ : ℝ) :
    let r := Real.exp (-(s*h))
    let z := Complex.exp ((θ : ℂ)*Complex.I)
    (∫ j : ℕ, Complex.exp ((((j : ℝ)*θ : ℝ) : ℂ)*Complex.I) ∂roundedDurationLaw h (expMeasure s)) =
      ((1+z)*(1 - (r : ℂ))) / (2*(1 - (r : ℂ)*z)) := by
  dsimp only
  let : IsProbabilityMeasure (expMeasure s) := isProbabilityMeasure_expMeasure hs
  rw [roundedDuration_characteristic_factor, exponentialDuration_floor_characteristic hs hh]
  rw [div_mul_div_comm]

/-- The real part of the full exponential count characteristic function
is nonnegative across the entire frequency interval. -/
theorem exponentialDuration_cosine_formula {s h : ℝ}
    (hs : 0 < s) (hh : 0 < h) (θ : ℝ) :
    let r := Real.exp (-(s*h))
    cosineSeries (countLawWeight (roundedDurationLaw h (expMeasure s))) θ =
      (1-r)^2*(1+Real.cos θ)/(2*(1+r^2-2*r*Real.cos θ)) := by
  dsimp only
  let : IsProbabilityMeasure (expMeasure s) := isProbabilityMeasure_expMeasure hs
  rw [countLaw_cosineSeries_eq_re_characteristic, exponentialDuration_rounded_characteristic hs hh]
  let r := Real.exp (-(s*h))
  let z := Complex.exp ((θ : ℂ)*Complex.I)
  let a := (1+z)*(1-(r : ℂ))
  let b := 2*(1-(r : ℂ)*z)
  change (a/b).re = _
  have hzr : z.re = Real.cos θ := Complex.exp_ofReal_mul_I_re θ
  have hzi : z.im = Real.sin θ := Complex.exp_ofReal_mul_I_im θ
  have har : a.re = (1+Real.cos θ)*(1-r) := by
    simp [a, Complex.mul_re, Complex.add_re, Complex.sub_re, hzr]
  have hai : a.im = Real.sin θ*(1-r) := by
    simp [a, Complex.mul_im, Complex.add_im, Complex.sub_im, hzi]
  have hbr : b.re = 2*(1-r*Real.cos θ) := by
    simp [b, Complex.mul_re, Complex.sub_re, hzr]
  have hbi : b.im = -(2*r*Real.sin θ) := by
    simp [b, Complex.mul_im, Complex.sub_im, hzi]
    ring
  set D := 1 + r^2 - 2*r*Real.cos θ
  have hsq : Complex.normSq b = 4*D := by
    rw [Complex.normSq_apply, hbr, hbi]
    dsimp only [D]
    linear_combination (4*r^2) * Real.sin_sq_add_cos_sq θ
  rw [Complex.div_re, hsq, har, hbr, hai, hbi, ← add_div]
  change _ = (1-r)^2*(1+Real.cos θ)/(2*D)
  have hnum : (1+Real.cos θ)*(1-r)*(2*(1-r*Real.cos θ)) +
      Real.sin θ*(1-r)*(-(2*r*Real.sin θ)) =
      2*((1-r)^2*(1+Real.cos θ)) := by
    linear_combination -(2*r*(1-r)) * Real.sin_sq_add_cos_sq θ
  rw [hnum, show 4*D = 2*(2*D) by ring]
  exact mul_div_mul_left _ _ (by norm_num)

theorem exponentialDuration_cosine_nonneg {s h : ℝ}
    (hs : 0 < s) (hh : 0 < h) (θ : ℝ) :
    0 ≤ cosineSeries (countLawWeight (roundedDurationLaw h (expMeasure s))) θ := by
  rw [exponentialDuration_cosine_formula hs hh]
  let r := Real.exp (-(s*h))
  have hr : 0 < r := Real.exp_pos _
  have hr₁ : r < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr (mul_pos hs hh))
  change 0 ≤ (1-r)^2*(1+Real.cos θ)/(2*(1+r^2-2*r*Real.cos θ))
  refine div_nonneg
    (mul_nonneg (sq_nonneg _) (by linarith only [Real.neg_one_le_cos θ])) ?_
  have hc := mul_le_mul_of_nonneg_left (Real.cos_le_one θ) (by positivity : 0 ≤ 2*r)
  nlinarith only [hc, sq_pos_of_pos (sub_pos.mpr hr₁)]

end BreakingResonance

#print axioms BreakingResonance.exponentialDuration_floorMass
#print axioms BreakingResonance.exponentialDuration_rounded_characteristic
#print axioms BreakingResonance.exponentialDuration_cosine_nonneg
