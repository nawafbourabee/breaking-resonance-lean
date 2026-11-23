import BreakingResonance.GaussianCrossingAngles
import PersistencePays.GaussianCovarianceMGF

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace BreakingResonance

def standardNormalPair : Measure (ℝ×ℝ) :=
  (gaussianReal 0 1).prod (gaussianReal 0 1)

instance : IsProbabilityMeasure standardNormalPair := by
  unfold standardNormalPair
  infer_instance

def standardNormalPairDensity (z : ℝ×ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((2*Real.pi)⁻¹*Real.exp (-(z.1^2+z.2^2)/2))

theorem standardNormalPair_eq_density :
    standardNormalPair = volume.withDensity standardNormalPairDensity := by
  unfold standardNormalPair
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num : (1:NNReal) ≠ 0),
    prod_withDensity (measurable_gaussianPDF _ _) (measurable_gaussianPDF _ _)]
  congr 1
  funext z
  change ENNReal.ofReal (gaussianPDFReal 0 1 z.1)*ENNReal.ofReal (gaussianPDFReal 0 1 z.2) =
    standardNormalPairDensity z
  rw [← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _)]
  congr 1
  simp only [gaussianPDFReal,NNReal.coe_one,mul_one,sub_zero,standardNormalPairDensity]
  rw [mul_mul_mul_comm,← mul_inv,← sq,Real.sq_sqrt (by positivity),← Real.exp_add]
  congr 2
  ring

def gaussianPolarRadial (r : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal r*ENNReal.ofReal ((2*Real.pi)⁻¹*Real.exp (-r^2/2))

theorem gaussianPolarRadial_measurable : Measurable gaussianPolarRadial := by
  unfold gaussianPolarRadial
  fun_prop

theorem gaussianPolar_density (p : ℝ×ℝ) :
    ENNReal.ofReal p.1 • standardNormalPairDensity (polarCoord.symm p) =
      gaussianPolarRadial p.1 := by
  unfold standardNormalPairDensity gaussianPolarRadial
  rw [smul_eq_mul]
  have h : (polarCoord.symm p).1^2+(polarCoord.symm p).2^2 = p.1^2 := by
    rw [polarCoord_symm_apply]
    simp only [Prod.fst,Prod.snd,mul_pow,← mul_add,Real.cos_sq_add_sin_sq,mul_one]
  rw [h]

theorem gaussianPolar_restrict {W : Set ℝ} (hW : MeasurableSet W) :
    (∫⁻ p in Ioi (0:ℝ) ×ˢ W, gaussianPolarRadial p.1 ∂(volume : Measure (ℝ×ℝ))) =
      (∫⁻ r in Ioi (0:ℝ), gaussianPolarRadial r) * volume W := by
  change (∫⁻ p in Ioi (0:ℝ) ×ˢ W, gaussianPolarRadial p.1 ∂(volume : Measure ℝ).prod volume) = _
  rw [setLIntegral_prod (fun p : ℝ×ℝ => gaussianPolarRadial p.1)
    ((gaussianPolarRadial_measurable.comp measurable_fst).aemeasurable)]
  simp_rw [lintegral_const,Measure.restrict_apply_univ]
  rw [lintegral_mul_const _ gaussianPolarRadial_measurable]

theorem gaussianPolar_radial_integral :
    (∫⁻ r in Ioi (0:ℝ), gaussianPolarRadial r) = (ENNReal.ofReal (2*Real.pi))⁻¹ := by
  have h := lintegral_comp_polarCoord_symm standardNormalPairDensity
  simp_rw [gaussianPolar_density] at h
  have hnorm : (∫⁻ p, standardNormalPairDensity p) = 1 := by
    rw [← setLIntegral_univ, ← withDensity_apply _ MeasurableSet.univ,
      ← standardNormalPair_eq_density,measure_univ]
  rw [hnorm] at h
  rw [polarCoord_target, gaussianPolar_restrict measurableSet_Ioo,Real.volume_Ioo,
    show Real.pi-(-Real.pi) = 2*Real.pi by ring] at h
  exact ENNReal.eq_inv_of_mul_eq_one_left h

def gaussianWedge (t : ℝ) : Set (ℝ×ℝ) :=
  {z | z.1 ≤ 0 ∧ 0 < Real.cos t*z.1+Real.sin t*z.2}

theorem gaussianWedge_measurable (t : ℝ) : MeasurableSet (gaussianWedge t) :=
  (measurableSet_le measurable_fst measurable_const).inter
    (measurableSet_lt measurable_const
      (show Measurable (fun z : ℝ×ℝ => Real.cos t*z.1+Real.sin t*z.2) by fun_prop))

set_option maxHeartbeats 800000 in
/-- On the polar chart, the Gaussian probability of crossing the initial
halfspace is bounded by the length of the angular window divided by 2π. -/
theorem gaussianWedge_probability {t : ℝ} (ht : 0 ≤ t) :
    standardNormalPair (gaussianWedge t) ≤ ENNReal.ofReal (t/(2*Real.pi)) := by
  let D := gaussianWedge t
  let W := crossingAngleWindow t
  let V := Ioi (0:ℝ) ×ˢ W
  have hD := gaussianWedge_measurable t
  have hV : MeasurableSet V := measurableSet_Ioi.prod (crossingAngleWindow_measurable t)
  have hsubset (p : ℝ×ℝ) (hp : p ∈ polarCoord.target)
      (hz : polarCoord.symm p ∈ D) : p ∈ V := by
    obtain ⟨hr,hφ⟩ := hp
    have hr₀ : 0 < p.1 := hr
    have hφ₀ : p.2 ∈ Ioo (-Real.pi) Real.pi := hφ
    have hleft : p.1*Real.cos p.2 ≤ 0 := hz.1
    have hright : 0 < Real.cos t*(p.1*Real.cos p.2)+Real.sin t*(p.1*Real.sin p.2) := hz.2
    have he : Real.cos t*(p.1*Real.cos p.2)+Real.sin t*(p.1*Real.sin p.2) =
        p.1*Real.cos (p.2-t) := by rw [Real.cos_sub]; ring
    rw [he] at hright
    exact ⟨hr,crossingAngle_mem_window ht hφ₀
      (nonpos_of_mul_nonpos_right hleft hr₀)
      (pos_of_mul_pos_right hright hr₀.le)⟩
  change standardNormalPair D ≤ _
  rw [standardNormalPair_eq_density,withDensity_apply _ hD,← lintegral_indicator hD,
    ← lintegral_comp_polarCoord_symm]
  have hle : (∫⁻ p in polarCoord.target,
        ENNReal.ofReal p.1 • D.indicator standardNormalPairDensity (polarCoord.symm p))
      ≤ ∫⁻ p in polarCoord.target, V.indicator (fun q => gaussianPolarRadial q.1) p := by
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem polarCoord.open_target.measurableSet] with p hp
    by_cases hp' : polarCoord.symm p ∈ D
    · rw [indicator_of_mem hp',indicator_of_mem (hsubset p hp hp'),gaussianPolar_density]
    · rw [indicator_of_notMem hp',smul_zero]
      exact zero_le
  apply hle.trans
  apply (lintegral_mono' Measure.restrict_le_self le_rfl).trans
  rw [lintegral_indicator hV,gaussianPolar_restrict (crossingAngleWindow_measurable t),
    gaussianPolar_radial_integral]
  refine (mul_le_mul_right crossingAngleWindow_volume _).trans_eq ?_
  rw [mul_comm,ENNReal.ofReal_div_of_pos (by positivity),div_eq_mul_inv]

end BreakingResonance

#print axioms BreakingResonance.standardNormalPair_eq_density
#print axioms BreakingResonance.gaussianPolar_radial_integral
#print axioms BreakingResonance.gaussianWedge_probability
