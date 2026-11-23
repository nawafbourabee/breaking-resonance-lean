import BreakingResonance.RoundedFourierLaw
import BreakingResonance.FourierTrig

/-! Non-resonance before rounding, and the effect of restricting the duration. -/
noncomputable section
namespace BreakingResonance
open MeasureTheory Set
open scoped ENNReal

/-- Definition 2.1, with the positive duration law represented as a measure
on the real line. The real part of its characteristic function is the
integral of the cosine. -/
structure NonresonantDuration (ρ : Measure ℝ) (m b δ : ℝ) : Prop where
  m_pos : 0 < m
  b_pos : 0 < b
  gap_pos : 0 < δ
  gap_le_one : δ ≤ 1
  positive_ae : ∀ᵐ τ ∂ρ, 0 < τ
  integrable_duration : Integrable (fun τ : ℝ => τ) ρ
  mean_le : (∫ τ : ℝ, τ ∂ρ) ≤ b / Real.sqrt m
  cosine_le : ∀ ω : ℝ, 2 * Real.sqrt m ≤ ω →
    (∫ τ : ℝ, Real.cos (ω*τ) ∂ρ) ≤ 1 - δ

def conditionalDurationLaw (ρ : Measure ℝ) (τstar : ℝ) : Measure ℝ :=
  (ρ (Iic τstar))⁻¹ • ρ.restrict (Iic τstar)

theorem integrable_duration_cos (ρ : Measure ℝ) [IsFiniteMeasure ρ] (ω : ℝ) :
    Integrable (fun τ : ℝ => Real.cos (ω*τ)) ρ :=
  Integrable.of_bound (by fun_prop) 1
    (Filter.Eventually.of_forall fun _ => Real.abs_cos_le_one _)

theorem retainedDuration_ne_zero (ρ : Measure ℝ) [IsProbabilityMeasure ρ] (τstar : ℝ)
    {δ : ℝ} (hδ : δ ≤ 1) (htail : (ρ (Ioi τstar)).toReal ≤ δ/4) :
    ρ (Iic τstar) ≠ 0 := by
  intro hcut
  have hc : ρ (Ioi τstar) = 1 := by
    rw [← compl_Iic, measure_compl measurableSet_Iic (measure_ne_top _ _), hcut,
      measure_univ, tsub_zero]
  rw [hc, ENNReal.toReal_one] at htail
  linarith

theorem conditionalDuration_isProbability (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    (τstar : ℝ) (hne : ρ (Iic τstar) ≠ 0) :
    IsProbabilityMeasure (conditionalDurationLaw ρ τstar) where
  measure_univ := by
    rw [conditionalDurationLaw, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_univ,
      ENNReal.inv_mul_cancel hne (measure_ne_top _ _)]

theorem conditionalDuration_positive_bounded (ρ : Measure ℝ) (τstar : ℝ)
    (hρ : ∀ᵐ τ ∂ρ, 0 < τ) :
    ∀ᵐ τ ∂conditionalDurationLaw ρ τstar, 0 < τ ∧ τ ≤ τstar := by
  have hpos : ∀ᵐ τ ∂ρ.restrict (Iic τstar), 0 < τ :=
    ae_mono Measure.restrict_le_self hρ
  exact Measure.ae_smul_measure (hpos.and (ae_restrict_mem measurableSet_Iic)) _

theorem conditionalDuration_one_sub_cos_lower (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    {m b δ : ℝ} (hρ : NonresonantDuration ρ m b δ) (τstar : ℝ)
    (htail : (ρ (Ioi τstar)).toReal ≤ δ/4) (ω : ℝ) (hω : 2 * Real.sqrt m ≤ ω) :
    δ/2 ≤ ∫ τ : ℝ, 1 - Real.cos (ω*τ) ∂conditionalDurationLaw ρ τstar := by
  let f (τ : ℝ) := 1 - Real.cos (ω*τ)
  have hf : Integrable f ρ := (integrable_const _).sub (integrable_duration_cos ρ ω)
  have hn (τ : ℝ) : 0 ≤ f τ := sub_nonneg.mpr (Real.cos_le_one _)
  have hp (τ : ℝ) : f τ ≤ 2 := by dsimp [f]; linarith [Real.neg_one_le_cos (ω*τ)]
  have htotal : δ ≤ ∫ τ, f τ ∂ρ := by
    dsimp only [f]
    rw [integral_sub (integrable_const _) (integrable_duration_cos ρ ω)]
    simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
    linarith [hρ.cosine_le ω hω]
  have hsplit := integral_add_compl (s := Iic τstar) measurableSet_Iic hf
  rw [compl_Iic] at hsplit
  have htailIntegral : (∫ τ in Ioi τstar, f τ ∂ρ) ≤ δ/2 := by
    refine (integral_mono hf.integrableOn (integrable_const (2 : ℝ)) hp).trans ?_
    simp only [integral_const, Measure.real, Measure.restrict_apply_univ, smul_eq_mul]
    linarith
  have hkept : δ/2 ≤ ∫ τ in Iic τstar, f τ ∂ρ := by linarith
  change δ/2 ≤ ∫ τ, f τ ∂conditionalDurationLaw ρ τstar
  rw [conditionalDurationLaw, integral_smul_measure, smul_eq_mul]
  have hinv : 1 ≤ ((ρ (Iic τstar))⁻¹).toReal := by
    have ht : (ρ (Iic τstar))⁻¹ ≠ ∞ :=
      ENNReal.inv_ne_top.mpr (retainedDuration_ne_zero ρ τstar hρ.gap_le_one htail)
    have hle : ρ (Iic τstar) ≤ 1 := by
      simpa only [measure_univ] using measure_mono (μ := ρ) (subset_univ (Iic τstar))
    simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono ht (ENNReal.one_le_inv.mpr hle)
  exact hkept.trans (le_mul_of_one_le_left (integral_nonneg hn) hinv)

/-- An even harmonic of a frequency controls the distances of its cosine
average from both 1 and -1. -/
theorem durationCosine_even_harmonic_gap (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    (k : ℕ) (hk : Even k) (u δ : ℝ)
    (hgap : δ ≤ ∫ τ : ℝ, 1 - Real.cos ((k : ℝ)*u*τ) ∂ρ) :
    δ ≤ (k : ℝ)^2 * (1 - ∫ τ : ℝ, Real.cos (u*τ) ∂ρ) ∧
    δ ≤ (k : ℝ)^2 * (1 + ∫ τ : ℝ, Real.cos (u*τ) ∂ρ) := by
  have hbase := (integrable_const (1 : ℝ)).sub (integrable_duration_cos ρ ((k : ℝ)*u))
  have hminus := (integrable_const (1 : ℝ)).sub (integrable_duration_cos ρ u)
  have hplus := (integrable_const (1 : ℝ)).add (integrable_duration_cos ρ u)
  have h₀ := integral_mono hbase (hminus.const_mul ((k : ℝ)^2)) fun τ => by
    change 1 - Real.cos (↑k*u*τ) ≤ ↑k^2 * (1 - Real.cos (u*τ))
    simpa only [mul_assoc] using one_sub_cos_nat_mul_le k (u*τ)
  have h₁ := integral_mono hbase (hplus.const_mul ((k : ℝ)^2)) fun τ => by
    change 1 - Real.cos (↑k*u*τ) ≤ ↑k^2 * (1 + Real.cos (u*τ))
    simpa only [mul_assoc] using one_sub_cos_even_mul_le k hk (u*τ)
  simp only [Pi.sub_apply, Pi.add_apply, integral_const_mul,
    integral_sub (integrable_const _) (integrable_duration_cos ρ u),
    integral_add (integrable_const _) (integrable_duration_cos ρ u),
    integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul] at h₀ h₁
  exact ⟨hgap.trans h₀, hgap.trans h₁⟩

/-- The intermediate-frequency estimate, with gap δ for the duration law
at the selected even harmonic. -/
theorem roundedDuration_intermediate_gap (h : ℝ) (hh : 0 < h) (ρ : Measure ℝ)
    [IsProbabilityMeasure ρ] (hpos : ∀ᵐ τ ∂ρ, 0 ≤ τ) (k : ℕ) (hk : Even k)
    (hkpos : 0 < k) (δ θ : ℝ)
    (hθ : |θ| ≤ δ / (2*(k : ℝ)^2))
    (hgap : δ ≤ ∫ τ : ℝ, 1 - Real.cos ((k : ℝ)*(|θ|/h)*τ) ∂ρ) :
    let ζ := δ / (2*(k : ℝ)^2)
    let C := cosineSeries (countLawWeight (roundedDurationLaw h ρ)) θ
    ζ ≤ 1 - C ∧ ζ ≤ 1 + C := by
  dsimp only
  have hharm := durationCosine_even_harmonic_gap ρ k hk (|θ|/h) δ hgap
  have hkreal : (0 : ℝ) < k := Nat.cast_pos.mpr hkpos
  have hksq : 0 < (k : ℝ)^2 := sq_pos_of_pos hkreal
  have he := roundedDuration_cosineSeries_error h hh ρ hpos θ
  have hcos (τ : ℝ) : Real.cos ((|θ|/h)*τ) = Real.cos ((τ/h)*θ) := by
    by_cases hθ₀ : 0 ≤ θ
    · rw [abs_of_nonneg hθ₀, show θ/h*τ = τ/h*θ by ring]
    · have hθ₁ : θ < 0 := lt_of_not_ge hθ₀
      rw [abs_of_neg hθ₁, show -θ/h*τ = -(τ/h*θ) by ring, Real.cos_neg]
  simp_rw [hcos] at hharm
  have hl : δ/(k : ℝ)^2 ≤ 1 - ∫ τ : ℝ, Real.cos (τ/h*θ) ∂ρ :=
    (div_le_iff₀ hksq).mpr (by rw [mul_comm]; exact hharm.1)
  have hu : δ/(k : ℝ)^2 ≤ 1 + ∫ τ : ℝ, Real.cos (τ/h*θ) ∂ρ :=
    (div_le_iff₀ hksq).mpr (by rw [mul_comm]; exact hharm.2)
  rw [abs_le] at he
  have hdiv : δ/(2*(k : ℝ)^2) = δ/(k : ℝ)^2/2 := by rw [div_div, mul_comm]
  rw [hdiv] at hθ ⊢
  exact ⟨by linarith [he.2], by linarith [he.1]⟩

/-- For the full count law, the first moment controls the lowest frequencies. -/
theorem roundedDuration_full_low (h : ℝ) (hh : 0 < h) (ρ : Measure ℝ)
    [IsProbabilityMeasure ρ] {m b δ : ℝ} (hρ : NonresonantDuration ρ m b δ)
    (hhm : h * Real.sqrt m ≤ 1) (θ : ℝ)
    (hθ : |θ| ≤ h * Real.sqrt m / (2*(b+1))) :
    (1/2 : ℝ) ≤ cosineSeries (countLawWeight (roundedDurationLaw h ρ)) θ := by
  let w := roundedDurationLaw h ρ
  have hpos : ∀ᵐ τ ∂ρ, 0 ≤ τ := hρ.positive_ae.mono fun _ hτ => hτ.le
  have hJ : Integrable (fun j : ℕ => (j : ℝ)) w :=
    (roundedDuration_integrable_mean h hh ρ hρ.integrable_duration hpos).1
  have hupper := (roundedDuration_mean_bounds h hh ρ hρ.integrable_duration hpos).2
  have hs : 0 < Real.sqrt m := Real.sqrt_pos.2 hρ.m_pos
  have hr : 0 < h * Real.sqrt m := mul_pos hh hs
  have hmean : (∫ j : ℕ, (j : ℝ) ∂w) ≤ (b+1)/(h * Real.sqrt m) := by
    calc
      _ ≤ (∫ τ : ℝ, τ ∂ρ)/h + 1/2 := hupper
      _ ≤ (b / Real.sqrt m)/h + 1/2 :=
        add_le_add (div_le_div_of_nonneg_right hρ.mean_le hh.le) le_rfl
      _ = b/(h * Real.sqrt m) + 1/2 := by rw [div_div, mul_comm (Real.sqrt m) h]
      _ ≤ (b+1)/(h * Real.sqrt m) := by
        rw [add_div]
        exact add_le_add le_rfl ((le_div_iff₀ hr).2 (by linarith))
  have hJi := (integrable_const (1 : ℝ)).sub (hJ.const_mul |θ|)
  have hcos : Integrable (fun j : ℕ => Real.cos ((j : ℝ)*θ)) w :=
    Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun _ => Real.abs_cos_le_one _)
  have hbound := integral_mono hJi hcos fun j => by
    have h := Real.abs_cos_sub_cos_le ((j : ℝ)*θ) 0
    have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
    rw [Real.cos_zero, sub_zero, abs_mul, abs_of_nonneg hj] at h
    change 1 - |θ| * (j : ℝ) ≤ Real.cos ((j : ℝ)*θ)
    linarith only [(abs_le.mp h).1]
  simp only [Pi.sub_apply, integral_sub (integrable_const _) (hJ.const_mul |θ|),
    integral_const_mul, integral_const, Measure.real, measure_univ, ENNReal.toReal_one,
    one_smul] at hbound
  have hprod : |θ| * (∫ j : ℕ, (j : ℝ) ∂w) ≤ 1/2 := by
    calc
      _ ≤ |θ| * ((b+1)/(h * Real.sqrt m)) :=
        mul_le_mul_of_nonneg_left hmean (abs_nonneg θ)
      _ ≤ (h * Real.sqrt m / (2*(b+1))) * ((b+1)/(h * Real.sqrt m)) :=
        mul_le_mul_of_nonneg_right hθ (div_nonneg (by linarith [hρ.b_pos]) hr.le)
      _ = 1/2 := by field_simp [hr.ne', show b + 1 ≠ 0 by linarith [hρ.b_pos]]
  rw [countLaw_cosineSeries_eq_integral_cos]
  exact (by linarith only [hprod] : (1/2 : ℝ) ≤ 1 - |θ| * ∫ j : ℕ, (j : ℝ) ∂w).trans hbound

end BreakingResonance

#print axioms BreakingResonance.conditionalDuration_one_sub_cos_lower
#print axioms BreakingResonance.durationCosine_even_harmonic_gap
#print axioms BreakingResonance.roundedDuration_intermediate_gap
#print axioms BreakingResonance.roundedDuration_full_low
