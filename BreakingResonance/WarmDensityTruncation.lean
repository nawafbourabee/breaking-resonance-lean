import BreakingResonance.DensityTotalVariation

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ProbabilityTheory ENNReal

namespace BreakingResonance

variable {S : Type*} [MeasurableSpace S]

theorem real_rnDeriv_withDensity (μ π : Measure S)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure π] (hac : μ ≪ π) :
    π.withDensity (fun x => ENNReal.ofReal ((μ.rnDeriv π x).toReal)) = μ := by
  rw [withDensity_congr_ae (g := μ.rnDeriv π)
    ((Measure.rnDeriv_lt_top μ π).mono fun _ hx => ENNReal.ofReal_toReal hx.ne),
      Measure.withDensity_rnDeriv_eq _ _ hac]

/-- Clip the initial density and retain a common submeasure when normalizing. -/
theorem warm_density_truncation
    (μ π : Measure S) [IsProbabilityMeasure μ] [IsProbabilityMeasure π]
    (hac : μ ≪ π) {M ε : ℝ} (hM : 0 ≤ M) (hε : 0 < ε) (hε₁ : ε ≤ 1)
    (hwarm : Real.sqrt (∫ x, (μ.rnDeriv π x).toReal^2 ∂π) ≤ M)
    (hL2 : MemLp (fun x => (μ.rnDeriv π x).toReal) 2 π) :
    ∃ f : S → ℝ, Measurable f ∧ (∀ x, 0 ≤ f x) ∧ (∀ x, f x ≤ 4*M^2/ε) ∧
      (∫ x, f x ∂π) = 1 ∧
      ∃ ξ : Measure S, ξ ≤ μ ∧ ξ ≤ π.withDensity (ENNReal.ofReal ∘ f) ∧
        1-ε/2 ≤ ξ.real univ := by
  let u (x : S) := (μ.rnDeriv π x).toReal
  have hu : Measurable u := (Measure.measurable_rnDeriv μ π).ennreal_toReal
  have hu₀ (x : S) : 0 ≤ u x := ENNReal.toReal_nonneg
  have hui : Integrable u π := hL2.integrable (by norm_num)
  have husq := (memLp_two_iff_integrable_sq hL2.aestronglyMeasurable).mp hL2
  have hw : (∫ x, (u x)^2 ∂π) ≤ M^2 :=
    (Real.sqrt_le_left hM).mp hwarm
  have hun : (∫ x, u x ∂π) = 1 := by
    have hn := withDensity_real_eq_setIntegral π hui hu₀ MeasurableSet.univ
    change (π.withDensity (fun x => ENNReal.ofReal (u x))).real univ = _ at hn
    rw [real_rnDeriv_withDensity μ π hac, probReal_univ,Measure.restrict_univ] at hn
    exact hn.symm
  have hu2 : 1 ≤ ∫ x, (u x)^2 ∂π := by
    have hV := variance_nonneg (X := u) (μ := π)
    rw [variance_eq_sub hL2,hun] at hV
    change 0 ≤ (∫ x, (u x)^2 ∂π)-1^2 at hV
    linarith
  have hMp : 0 < M := by nlinarith only [hM, hw, hu2]
  let cap := 2*M^2/ε
  have hcap : 0 < cap := by dsimp [cap]; positivity
  let clipped (x : S) := min (u x) cap
  have hc : Measurable clipped := hu.min measurable_const
  have hc0 (x : S) : 0 ≤ clipped x := le_min (hu₀ x) hcap.le
  have hci : Integrable clipped π :=
    markovAction_integrable_bound hc hc0 (fun x => min_le_right _ _)
  let Z := ∫ x, clipped x ∂π
  have hZupper : Z ≤ 1 := by
    rw [← hun]
    exact integral_mono hci hui (fun x => min_le_left _ _)
  have htail (x : S) : u x-clipped x ≤ (u x)^2/cap := by
    by_cases hx : u x ≤ cap
    · simp [clipped, min_eq_left hx, div_nonneg (sq_nonneg _) hcap.le]
    · have hxu : cap ≤ u x := le_of_not_ge hx
      dsimp [clipped]
      rw [min_eq_right hxu]
      apply (le_div_iff₀ hcap).mpr
      nlinarith only [mul_le_mul_of_nonneg_right hxu (hu₀ x), sq_nonneg cap]
  have htail_i : (∫ x, u x-clipped x ∂π) ≤ (∫ x, (u x)^2/cap ∂π) :=
    integral_mono (hui.sub hci) (husq.div_const cap) htail
  rw [integral_sub hui hci, hun, integral_div] at htail_i
  have hmass : 1-ε/2 ≤ Z := by
    have hm := div_le_div_of_nonneg_right hw hcap.le
    have he : M^2/cap = ε/2 := by dsimp [cap]; field_simp
    rw [he] at hm
    have hclean : 1-Z ≤ (∫ x, (u x)^2 ∂π)/cap := htail_i
    linarith only [hclean,hm]
  have hZhalf : (1/2:ℝ) ≤ Z := by linarith only [hmass,hε₁]
  have hZ : 0 < Z := lt_of_lt_of_le (by norm_num) hZhalf
  let f (x : S) := Z⁻¹ * clipped x
  have hf : Measurable f := measurable_const.mul hc
  have hf0 (x : S) : 0 ≤ f x := mul_nonneg (inv_nonneg.mpr hZ.le) (hc0 x)
  have hfC (x : S) : f x ≤ 4*M^2/ε := by
    have hinv : Z⁻¹ ≤ 2 := by
      exact (inv_le_iff_one_le_mul₀ hZ).mpr (by linarith only [hZhalf])
    calc
      f x ≤ 2*clipped x := mul_le_mul_of_nonneg_right hinv (hc0 x)
      _ ≤ 2*cap := mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num)
      _ = _ := by dsimp [cap]; ring
  have hmean : (∫ x, f x ∂π) = 1 := by
    dsimp [f]
    rw [integral_const_mul]
    exact inv_mul_cancel₀ hZ.ne'
  let ξ := π.withDensity (ENNReal.ofReal ∘ clipped)
  have hξμ : ξ ≤ μ := by
    rw [← real_rnDeriv_withDensity μ π hac]
    exact withDensity_mono (Filter.Eventually.of_forall fun x =>
      ENNReal.ofReal_le_ofReal (min_le_left _ _))
  have hξf : ξ ≤ π.withDensity (ENNReal.ofReal ∘ f) := by
    apply withDensity_mono
    refine Filter.Eventually.of_forall fun x => ENNReal.ofReal_le_ofReal ?_
    have hv : 1 ≤ Z⁻¹ := one_le_inv_iff₀.mpr ⟨hZ,hZupper⟩
    simpa [f] using mul_le_mul_of_nonneg_right hv (hc0 x)
  have hξZ : ξ.real univ = Z := by
    rw [withDensity_real_eq_setIntegral π hci hc0 MeasurableSet.univ,Measure.restrict_univ]
  exact ⟨f,hf,hf0,hfC,hmean,ξ,hξμ,hξf,by rw [hξZ]; exact hmass⟩

end BreakingResonance

#print axioms BreakingResonance.warm_density_truncation
