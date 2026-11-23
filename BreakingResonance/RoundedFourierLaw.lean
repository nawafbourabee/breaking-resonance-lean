import BreakingResonance.KernelQuadratic
import BreakingResonance.RoundingCost
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! Characteristic functions of the paper's rounded duration law. -/
noncomputable section
namespace BreakingResonance
open MeasureTheory Set
open scoped ENNReal

/-- Integration against the count law separates the two values of the fair
Bernoulli draw. -/
theorem roundedDuration_integral_bounded {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
    (h : ℝ) (ρ : Measure ℝ) [IsProbabilityMeasure ρ] (f : ℕ → V)
    (C : ℝ) (hf : ∀ j, ‖f j‖ ≤ C) :
    (∫ j, f j ∂roundedDurationLaw h ρ) =
      (1/2 : ℝ) • (∫ τ : ℝ, f (Nat.floor (τ/h)) ∂ρ) +
      (1/2 : ℝ) • (∫ τ : ℝ, f (Nat.floor (τ/h) + 1) ∂ρ) := by
  let T := fun τ : ℝ => Nat.floor (τ/h)
  let T₁ := fun τ : ℝ => Nat.floor (τ/h) + 1
  have hT : Measurable T := measurable_floorDuration h
  have hT₁ : Measurable T₁ := measurable_succFloorDuration h
  have hm (S : ℝ → ℕ) : AEStronglyMeasurable f (ρ.map S) :=
    (measurable_of_countable f).aestronglyMeasurable
  have hI (S : ℝ → ℕ) (hS : Measurable S) : Integrable f (ρ.map S) := by
    apply (integrable_map_measure (hm S) hS.aemeasurable).mpr
    exact Integrable.of_bound ((measurable_of_countable f).comp hS).aestronglyMeasurable C
      (Filter.Eventually.of_forall fun τ => hf (S τ))
  have hhalf : (1/2 : ℝ≥0∞) ≠ ∞ := by norm_num
  rw [roundedDurationLaw, integral_add_measure ((hI T hT).smul_measure hhalf)
    ((hI T₁ hT₁).smul_measure hhalf), integral_smul_measure, integral_smul_measure,
    integral_map hT.aemeasurable (hm T), integral_map hT₁.aemeasurable (hm T₁)]
  norm_num
  rfl

/-- The Bernoulli multiplier in the characteristic function of the
numerical integration time, expressed as a function of the integer count. -/
theorem roundedDuration_characteristic_factor (h : ℝ) (ρ : Measure ℝ)
    [IsProbabilityMeasure ρ] (θ : ℝ) :
    (∫ j : ℕ, Complex.exp (((j : ℝ) * θ : ℝ) * Complex.I) ∂roundedDurationLaw h ρ) =
      ((1 + Complex.exp ((θ : ℂ) * Complex.I))/2) *
        (∫ τ : ℝ, Complex.exp ((((Nat.floor (τ/h) : ℝ) * θ : ℝ) : ℂ) * Complex.I) ∂ρ) := by
  let f (j : ℕ) := Complex.exp (((j : ℝ) * θ : ℝ) * Complex.I)
  let F (τ : ℝ) := f (Nat.floor (τ/h))
  change (∫ j : ℕ, f j ∂roundedDurationLaw h ρ) = _ * ∫ τ, F τ ∂ρ
  rw [roundedDuration_integral_bounded h ρ f 1 (fun j => (Complex.norm_exp_ofReal_mul_I _).le)]
  have hF (τ : ℝ) :
      f (Nat.floor (τ/h)+1) = Complex.exp ((θ : ℂ) * Complex.I) * F τ := by
    dsimp only [F, f]
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp_rw [hF, integral_const_mul]
  rw [RCLike.real_smul_eq_coe_mul, RCLike.real_smul_eq_coe_mul]
  push_cast
  ring

theorem bernoulliMultiplier_norm (θ : ℝ) (hθ : |θ| ≤ Real.pi) :
    ‖(1 + Complex.exp ((θ : ℂ) * Complex.I))/2‖ = Real.cos (θ/2) := by
  let z := Complex.exp ((θ : ℂ) * Complex.I)
  change ‖(1 + z)/2‖ = _
  have hcos : 0 ≤ Real.cos (θ/2) := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [(abs_le.mp hθ).1], by linarith [(abs_le.mp hθ).2]⟩
  apply (sq_eq_sq₀ (norm_nonneg _) hcos).mp
  have hz : Complex.normSq z = 1 := by
    rw [← Complex.sq_norm, show ‖z‖ = 1 from Complex.norm_exp_ofReal_mul_I θ, one_pow]
  have hzr : z.re = Real.cos θ := Complex.exp_ofReal_mul_I_re θ
  have hdouble := Real.cos_two_mul (θ/2)
  rw [show 2 * (θ/2) = θ by ring] at hdouble
  rw [Complex.sq_norm, Complex.normSq_div, Complex.normSq_add, hz]
  simp only [Complex.normSq_one, one_mul, Complex.conj_re, hzr]
  rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_cast, Complex.normSq_ofReal]
  nlinarith only [hdouble]

/-- The common high-frequency estimate for the conditional and full count laws. -/
theorem roundedDuration_abs_cosineSeries_high (h : ℝ) (ρ : Measure ℝ)
    [IsProbabilityMeasure ρ] {ζ θ : ℝ} (hζ : 0 ≤ ζ) (hζθ : ζ ≤ |θ|) (hθ : |θ| ≤ Real.pi) :
    |cosineSeries (countLawWeight (roundedDurationLaw h ρ)) θ| ≤ Real.cos (ζ/2) := by
  rw [countLaw_cosineSeries_eq_re_characteristic, roundedDuration_characteristic_factor]
  refine (Complex.abs_re_le_norm _).trans ?_
  rw [norm_mul, bernoulliMultiplier_norm θ hθ]
  have hc : 0 ≤ Real.cos (θ/2) := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [(abs_le.mp hθ).1], by linarith [(abs_le.mp hθ).2]⟩
  have hI : ‖∫ τ : ℝ, Complex.exp ((((Nat.floor (τ/h) : ℝ) * θ : ℝ) : ℂ) * Complex.I) ∂ρ‖
      ≤ 1 := by
    have hb : ∀ᵐ τ : ℝ ∂ρ,
        ‖Complex.exp ((((Nat.floor (τ/h) : ℝ) * θ : ℝ) : ℂ) * Complex.I)‖ ≤ 1 :=
      Filter.Eventually.of_forall fun _ => (Complex.norm_exp_ofReal_mul_I _).le
    simpa only [Measure.real, measure_univ, ENNReal.toReal_one, mul_one] using
      norm_integral_le_of_norm_le_const hb
  calc
    _ ≤ Real.cos (θ/2) := mul_le_of_le_one_right hc hI
    _ = Real.cos (|θ|/2) := by
      have ha : |θ/2| = |θ|/2 := by rw [abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      rw [← ha, Real.cos_abs]
    _ ≤ Real.cos (ζ/2) :=
      Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos]) (by linarith)

theorem floorDuration_abs_error (s : ℝ) (hs : 0 ≤ s) :
    |(Nat.floor s : ℝ) - s| ≤ 1 ∧ |((Nat.floor s + 1 : ℕ) : ℝ) - s| ≤ 1 := by
  have hl := Nat.floor_le hs
  have hu := Nat.lt_floor_add_one s
  push_cast
  exact ⟨abs_le.mpr ⟨by linarith, by linarith⟩, abs_le.mpr ⟨by linarith, by linarith⟩⟩

theorem countLaw_cosineSeries_eq_integral_cos (w : Measure ℕ) [IsProbabilityMeasure w] (θ : ℝ) :
    cosineSeries (countLawWeight w) θ = ∫ j : ℕ, Real.cos ((j : ℝ) * θ) ∂w := by
  have hi : Integrable (fun j : ℕ => Real.cos ((j : ℝ) * θ)) w := by
    apply Integrable.of_bound (Measurable.aestronglyMeasurable (measurable_of_countable _)) 1
    filter_upwards with j
    exact Real.abs_cos_le_one _
  rw [integral_countable hi]
  rfl

/-- Rounding changes the mean cosine by at most the magnitude of the count frequency. -/
theorem roundedDuration_cosineSeries_error (h : ℝ) (hh : 0 < h) (ρ : Measure ℝ)
    [IsProbabilityMeasure ρ] (hpos : ∀ᵐ τ ∂ρ, 0 ≤ τ) (θ : ℝ) :
    |cosineSeries (countLawWeight (roundedDurationLaw h ρ)) θ -
      (∫ τ : ℝ, Real.cos ((τ/h)*θ) ∂ρ)| ≤ |θ| := by
  let f (j : ℕ) := Real.cos ((j : ℝ) * θ)
  let g (τ : ℝ) := Real.cos ((τ/h)*θ)
  rw [countLaw_cosineSeries_eq_integral_cos]
  change |(∫ j, f j ∂roundedDurationLaw h ρ) - (∫ τ, g τ ∂ρ)| ≤ |θ|
  rw [roundedDuration_integral_bounded h ρ f 1 (fun _ => Real.abs_cos_le_one _)]
  have hI : Integrable g ρ := Integrable.of_bound (by dsimp [g]; fun_prop) 1
    (Filter.Eventually.of_forall fun _ => Real.abs_cos_le_one _)
  have hdiff (T : ℝ → ℕ) (hT : Measurable T)
      (hclose : ∀ᵐ τ ∂ρ, |(T τ : ℝ) - τ/h| ≤ 1) :
      |(∫ τ, f (T τ) ∂ρ) - (∫ τ, g τ ∂ρ)| ≤ |θ| := by
    have hf : Integrable (f ∘ T) ρ := Integrable.of_bound
      ((measurable_of_countable f).comp hT).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun _ => Real.abs_cos_le_one _)
    have he := integral_sub hf hI
    simp only [Function.comp_apply] at he
    rw [← he]
    have hb : ∀ᵐ τ ∂ρ, ‖f (T τ) - g τ‖ ≤ |θ| := by
      filter_upwards [hclose] with τ hτ
      change |Real.cos ((T τ : ℝ)*θ) - Real.cos ((τ/h)*θ)| ≤ _
      apply (Real.abs_cos_sub_cos_le _ _).trans
      rw [← sub_mul, abs_mul]
      exact mul_le_of_le_one_left (abs_nonneg θ) hτ
    simpa only [Measure.real, measure_univ, ENNReal.toReal_one, mul_one, Real.norm_eq_abs] using
      norm_integral_le_of_norm_le_const hb
  have h₀ := hdiff _ (measurable_floorDuration h)
    (hpos.mono fun _ ht => (floorDuration_abs_error _ (div_nonneg ht hh.le)).1)
  have h₁ := hdiff _ (measurable_succFloorDuration h)
    (hpos.mono fun _ ht => (floorDuration_abs_error _ (div_nonneg ht hh.le)).2)
  rw [smul_eq_mul, smul_eq_mul, abs_le] at *
  constructor <;> linarith [h₀.1, h₀.2, h₁.1, h₁.2]

end BreakingResonance

#print axioms BreakingResonance.roundedDuration_integral_bounded
#print axioms BreakingResonance.roundedDuration_characteristic_factor
#print axioms BreakingResonance.roundedDuration_abs_cosineSeries_high
#print axioms BreakingResonance.roundedDuration_cosineSeries_error
