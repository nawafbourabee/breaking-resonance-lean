import BreakingResonance.DurationNonresonance

/-! The low-frequency estimate for the conditional duration law. -/
noncomputable section
namespace BreakingResonance
open MeasureTheory Set

/-- If a rounded count is within one of the unrounded count, its square
controls the square of the unrounded count up to an additive error. -/
theorem roundedCount_sq_lower {t j : ℝ} (hd : |j - t| ≤ 1) :
    t^2 / 2 - 1 ≤ j^2 := by
  have hd₂ : (j - t)^2 ≤ 1 := by
    simpa only [sq_abs, one_pow] using
      (sq_le_sq₀ (abs_nonneg (j - t)) zero_le_one).mpr hd
  nlinarith only [hd₂, sq_nonneg (t - 2*j)]

/-- Lemma 5.3 at frequencies at most h√m/(1 + √m τstar). -/
theorem roundedDuration_conditional_low (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    {m b δ : ℝ} (hρ : NonresonantDuration ρ m b δ) (τstar : ℝ) (hcut : 0 < τstar)
    (htail : (ρ (Ioi τstar)).toReal ≤ δ/4) (h : ℝ) (hh : 0 < h)
    (hhm : h^2*m ≤ δ/16) (θ : ℝ)
    (hθ : |θ| ≤ h*Real.sqrt m / (Real.sqrt m*τstar + 1)) :
    (δ/64) * (θ^2/(h^2*m)) ≤
      1 - cosineSeries (countLawWeight (roundedDurationLaw h (conditionalDurationLaw ρ τstar))) θ ∧
    Real.cos 1 ≤
      cosineSeries (countLawWeight (roundedDurationLaw h (conditionalDurationLaw ρ τstar))) θ := by
  let ν := conditionalDurationLaw ρ τstar
  let : IsProbabilityMeasure ν :=
    conditionalDuration_isProbability ρ τstar (retainedDuration_ne_zero ρ τstar hρ.gap_le_one htail)
  have hν : ∀ᵐ τ ∂ν, 0 < τ ∧ τ ≤ τstar :=
    conditionalDuration_positive_bounded ρ τstar hρ.positive_ae
  set r := h * Real.sqrt m with hr_eq
  have hs : 0 < Real.sqrt m := Real.sqrt_pos.2 hρ.m_pos
  have hr : 0 < r := mul_pos hh hs
  have hr₂ : r^2 = h^2*m := by rw [hr_eq, mul_pow, Real.sq_sqrt hρ.m_pos.le]
  have hr₁ : r ≤ 1 := by
    apply (sq_le_sq₀ hr.le zero_le_one).mp
    rw [hr₂]
    linarith only [hhm, hρ.gap_le_one]
  have hband : 0 < Real.sqrt m*τstar + 1 := by positivity
  have hθband : |θ| * (Real.sqrt m*τstar + 1) ≤ r := (le_div_iff₀ hband).mp hθ
  let g (τ : ℝ) := (τ/h)^2
  have hg : Integrable g ν := Integrable.of_bound (by dsimp [g]; fun_prop) ((τstar/h)^2)
    (hν.mono fun τ hτ => by
      change |(τ/h)^2| ≤ _
      rw [abs_of_nonneg (sq_nonneg _)]
      exact (sq_le_sq₀ (div_nonneg hτ.1.le hh.le) (div_nonneg hcut.le hh.le)).mpr
        (div_le_div_of_nonneg_right hτ.2 hh.le))
  have hgap := conditionalDuration_one_sub_cos_lower ρ hρ τstar htail
    (2 * Real.sqrt m) le_rfl
  have hmoment : δ/2 ≤ (2*r^2) * (∫ τ, g τ ∂ν) := by
    refine hgap.trans ?_
    rw [← integral_const_mul]
    exact integral_mono ((integrable_const _).sub (integrable_duration_cos ν _))
      (hg.const_mul (2*r^2)) fun τ => by
        have hb := one_sub_cos_le_sq_div_two (2 * Real.sqrt m * τ)
        change 1 - Real.cos (2 * Real.sqrt m * τ) ≤ (2*r^2) * (τ/h)^2
        convert hb using 1
        rw [hr_eq]
        field_simp [hh.ne']
  let f (j : ℕ) := Real.cos ((j : ℝ)*θ)
  let a (τ : ℝ) := (θ^2/4) * (g τ / 2 - 1)
  have ha : Integrable a ν :=
    (((hg.div_const 2).sub (integrable_const (1 : ℝ))).const_mul (θ^2/4))
  have hpoint (T : ℝ → ℕ) (hT : Measurable T)
      (hnear : ∀ τ : ℝ, 0 ≤ τ → |(T τ : ℝ) - τ/h| ≤ 1) :
      (∫ τ, a τ ∂ν) ≤ 1 - (∫ τ, f (T τ) ∂ν) ∧
      Real.cos 1 ≤ (∫ τ, f (T τ) ∂ν) := by
    have hi : Integrable (fun τ => f (T τ)) ν :=
      Integrable.of_bound ((measurable_of_countable f).comp hT).aestronglyMeasurable 1
        (Filter.Eventually.of_forall fun _ => Real.abs_cos_le_one _)
    have hangle : ∀ᵐ τ ∂ν, |(T τ : ℝ)*θ| ≤ 1 := hν.mono fun τ hτ => by
      have hj : (T τ : ℝ) ≤ τ/h + 1 := by linarith [(abs_le.mp (hnear τ hτ.1.le)).2]
      have hjr : r * (T τ : ℝ) ≤ Real.sqrt m*τstar + 1 := by
        calc
          _ ≤ r*(τ/h + 1) := mul_le_mul_of_nonneg_left hj hr.le
          _ = Real.sqrt m*τ + r := by rw [hr_eq]; field_simp [hh.ne']
          _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hτ.2 hs.le) hr₁
      rw [abs_mul, abs_of_nonneg (show 0 ≤ (T τ : ℝ) by positivity)]
      apply (le_of_mul_le_mul_left _ hr)
      calc
        r * ((T τ : ℝ)*|θ|) = (r*(T τ : ℝ))*|θ| := by ring
        _ ≤ (Real.sqrt m*τstar+1)*|θ| := mul_le_mul_of_nonneg_right hjr (abs_nonneg θ)
        _ ≤ r*1 := by rw [mul_one, mul_comm]; exact hθband
    constructor
    · have he := integral_mono_ae ha ((integrable_const (1 : ℝ)).sub hi) (by
        filter_upwards [hν, hangle] with τ hτ ht
        change (θ^2/4) * ((τ/h)^2/2 - 1) ≤ 1 - Real.cos ((T τ : ℝ)*θ)
        calc
          _ ≤ (θ^2/4) * (T τ : ℝ)^2 :=
            mul_le_mul_of_nonneg_left (roundedCount_sq_lower (hnear τ hτ.1.le)) (by positivity)
          _ = ((T τ : ℝ)*θ)^2/4 := by ring
          _ ≤ _ := sq_div_four_le_one_sub_cos ht)
      simpa only [Pi.sub_apply, integral_sub (integrable_const _) hi, integral_const,
        probReal_univ, one_smul] using he
    · have he := integral_mono_ae (integrable_const (Real.cos 1)) hi (by
        filter_upwards [hangle] with τ ht
        change Real.cos 1 ≤ Real.cos ((T τ : ℝ)*θ)
        rw [← Real.cos_abs ((T τ : ℝ)*θ)]
        exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_gt_three]) ht)
      simpa only [integral_const, probReal_univ, one_smul] using he
  have h₀ := hpoint _ (measurable_floorDuration h)
    (fun _ ht => (floorDuration_abs_error _ (div_nonneg ht hh.le)).1)
  have h₁ := hpoint _ (measurable_succFloorDuration h)
    (fun _ ht => (floorDuration_abs_error _ (div_nonneg ht hh.le)).2)
  have ha_lower : (δ/64) * (θ^2/(h^2*m)) ≤ ∫ τ, a τ ∂ν := by
    have hsq : 0 < r^2 := sq_pos_of_pos hr
    have hdiv : δ / (4*r^2) ≤ ∫ τ, g τ ∂ν := by
      apply (div_le_iff₀ (by positivity : 0 < 4*r^2)).mpr
      nlinarith only [hmoment]
    have hincr : δ/(16*r^2) ≤ (∫ τ, g τ ∂ν) / 2 - 1 := by
      have hmin : 1 ≤ δ/(16*r^2) := by
        apply (le_div_iff₀ (by positivity : 0 < 16*r^2)).mpr
        rw [hr₂]
        linarith only [hhm]
      have hid : δ/(4*r^2) = 4*(δ/(16*r^2)) := by
        field_simp [hsq.ne']
        ring
      linarith only [hdiv, hid, hmin]
    change _ ≤ ∫ τ, (θ^2/4) * (g τ / 2 - 1) ∂ν
    rw [integral_const_mul, integral_sub (hg.div_const 2) (integrable_const _),
      integral_div, integral_const, probReal_univ, one_smul, ← hr₂]
    calc
      _ = (θ^2/4) * (δ/(16*r^2)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hincr (by positivity)
  rw [countLaw_cosineSeries_eq_integral_cos]
  change _ ≤ 1 - (∫ j, f j ∂roundedDurationLaw h ν) ∧
    _ ≤ (∫ j, f j ∂roundedDurationLaw h ν)
  rw [roundedDuration_integral_bounded h ν f 1 (fun _ => Real.abs_cos_le_one _)]
  simp only [smul_eq_mul]
  exact ⟨ha_lower.trans (by linarith only [h₀.1, h₁.1]), by linarith only [h₀.2, h₁.2]⟩

end BreakingResonance

#print axioms BreakingResonance.roundedCount_sq_lower
#print axioms BreakingResonance.roundedDuration_conditional_low
