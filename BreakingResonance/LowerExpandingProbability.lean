import BreakingResonance.LowerExpandingVolume
import BreakingResonance.AdjustedFlow
import Mathlib.Analysis.Complex.ExponentialBounds

noncomputable section

open MeasureTheory Set PersistencePays
open scoped ENNReal

namespace BreakingResonance

theorem fastPotential_continuous (curvNeg curvPos : ℝ) :
    Continuous (fastPotential curvNeg curvPos) :=
  continuous_iff_continuousAt.mpr fun x => (fastPotential_hasDerivAt curvNeg curvPos x).continuousAt

theorem fastPotential_gibbs_integrable {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Integrable (fun x => Real.exp (-fastPotential a b x)) volume := by
  refine (integrable_exp_neg_mul_sq (show 0 < a/2 by positivity)).mono'
    (Real.continuous_exp.comp (fastPotential_continuous a b).neg).aestronglyMeasurable (ae_of_all _ (fun x => ?_))
  rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
  apply Real.exp_le_exp.mpr
  unfold fastPotential
  split_ifs <;> nlinarith only [mul_le_mul_of_nonneg_right hab (sq_nonneg x)]

/-- Split the normalizing integral on the two half-lines. The discontinuity
in curvature only affects the two scale factors. -/
theorem fastPotential_normalizer {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ x, Real.exp (-fastPotential a b x)) =
      (Real.sqrt (Real.pi/(a/2))+Real.sqrt (Real.pi/(b/2)))/2 := by
  have hI : MeasurableSet (Ioi (0:ℝ)) := measurableSet_Ioi
  rw [← integral_add_compl hI (fastPotential_gibbs_integrable ha hab)]
  rw [compl_Ioi]
  have hpos : (∫ x in Ioi (0:ℝ), Real.exp (-fastPotential a b x)) =
      Real.sqrt (Real.pi/(b/2))/2 := by
    rw [← integral_gaussian_Ioi (b/2)]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    change Real.exp (-(if 0 ≤ x then b*x^2/2 else a*x^2/2)) = _
    rw [ite_eq_left (le_of_lt hx)]
    congr 1
    ring
  have hneg : (∫ x in Iic (0:ℝ), Real.exp (-fastPotential a b x)) =
      Real.sqrt (Real.pi/(a/2))/2 := by
    rw [← integral_gaussian_Ioi (a/2)]
    have he := integral_comp_neg_Ioi (0:ℝ) (fun x => Real.exp (-fastPotential a b x))
    rw [neg_zero] at he
    rw [← he]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    have hneg : ¬ 0 ≤ -x := not_le.mpr (neg_neg_of_pos hx)
    change Real.exp (-(if 0 ≤ -x then b*(-x)^2/2 else a*(-x)^2/2)) = _
    rw [ite_eq_right hneg]
    congr 1
    ring
  rw [hpos,hneg]
  ring

theorem fastPhase_normalizer_bound {a b : ℝ}
    (ha : 1/64 ≤ a) (hb : 1/16 ≤ b) (hab : a ≤ b) :
    (∫ z, Real.exp (-phaseEnergy (fastPotential a b) z)
      ∂((volume : Measure ℝ).prod volume)) ≤ 12*Real.pi := by
  have ha₀ : 0 < a := by linarith only [ha]
  have hb₀ : 0 < b := ha₀.trans_le hab
  have hsplit : (fun z : ℝ×ℝ => Real.exp (-phaseEnergy (fastPotential a b) z)) =
    fun z => Real.exp (-fastPotential a b z.1)*Real.exp (-(1/2:ℝ)*z.2^2) := by
    funext z
    rw [← Real.exp_add,phaseEnergy_eq_norm,Real.norm_eq_abs,sq_abs]
    congr 1
    ring
  rw [hsplit,integral_prod_mul (fun x : ℝ => Real.exp (-fastPotential a b x))
    (fun v : ℝ => Real.exp (-(1/2:ℝ)*v^2)),fastPotential_normalizer ha₀ hab,integral_gaussian]
  have hπ := Real.pi_pos
  have hvehA : Real.pi/(a/2) ≤ 64*(Real.pi/(1/2)) := by
    apply (div_le_iff₀ (show 0 < a/2 by positivity)).mpr
    have hp := mul_le_mul_of_nonneg_left ha hπ.le
    nlinarith only [hp]
  have hvehB : Real.pi/(b/2) ≤ 16*(Real.pi/(1/2)) := by
    apply (div_le_iff₀ (show 0 < b/2 by positivity)).mpr
    have hp := mul_le_mul_of_nonneg_left hb hπ.le
    nlinarith only [hp]
  have hsqA := Real.sqrt_le_sqrt hvehA
  have hsqB := Real.sqrt_le_sqrt hvehB
  rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 64),
    show Real.sqrt 64 = 8 by norm_num] at hsqA
  rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 16),
    show Real.sqrt 16 = 4 by norm_num] at hsqB
  have hsum : (Real.sqrt (Real.pi/(a/2))+Real.sqrt (Real.pi/(b/2)))/2 ≤
    6*Real.sqrt (Real.pi/(1/2)) := by linarith only [hsqA,hsqB]
  have hm := mul_le_mul_of_nonneg_right hsum (Real.sqrt_nonneg (Real.pi/(1/2)))
  have he := Real.sq_sqrt (show 0 ≤ Real.pi/(1/2) by positivity)
  nlinarith only [hm,he]

private theorem qstar_numeric : (1/1000:ℝ) ≤ (9/1200)*Real.exp (-2) := by
  have hE : Real.exp 1 ≤ (2.72:ℝ) := Real.exp_one_lt_d9.le.trans (by norm_num)
  have hE₂ : Real.exp 2 ≤ 15/2 := by
    rw [show (2:ℝ) = 1+1 by norm_num,Real.exp_add]
    have hs := (sq_le_sq₀ (Real.exp_nonneg 1) (by norm_num : (0:ℝ) ≤ 2.72)).mpr hE
    nlinarith only [hs]
  rw [Real.exp_neg,← div_eq_mul_inv]
  apply (le_div_iff₀ (Real.exp_pos _)).mpr
  linarith only [hE₂]

set_option maxHeartbeats 800000 in
/-- The expanding set has probability at least q_* under the actual scalar
position Gibbs law and standard Gaussian momentum. -/
theorem expandingSet_gibbs_probability {h : ℝ} (hh : 0 < h) (hh₁ : h ≤ 1) {δ : ℝ}
    (hδ : 0 < δ) (hδp : δ ≤ 1/(80*(cycleHalfLength h:ℝ)^2)) :
    let p := cycleHalfLength h
    ENNReal.ofReal (1/1000) ≤ (phaseGibbs (asymmetricPotential h p δ)) (expandingSet h p δ) := by
  let p := cycleHalfLength h
  let a := curvatureForAngle h (fastAngleNeg p δ)
  let b := curvatureForAngle h (fastAnglePos p δ)
  let U := asymmetricPotential h p δ
  let E := expandingSet h p δ
  let μ : Measure (ℝ×ℝ) := (volume : Measure ℝ).prod volume
  let Z := ∫ z, Real.exp (-phaseEnergy U z) ∂μ
  obtain ⟨hp,hph,_⟩ := cycleHalfLength_bounds hh hh₁
  obtain ⟨hb,_,ha,hab⟩ := fastCurvature_bounds hh hh₁ hδ hδp
  have ha₀ : 0 < a := (by norm_num : 0 < (1/64:ℝ)).trans_le ha
  have hU : Measurable U := (fastPotential_continuous a b).measurable
  have hi : Integrable (fun x => Real.exp (-U x)) volume := fastPotential_gibbs_integrable ha₀ hab.le
  have hZ : 0 < Z := integral_exp_pos (phase_gibbs_integrable U hi)
  have hZu : Z ≤ 12*Real.pi := fastPhase_normalizer_bound ha hb hab.le
  have hE : MeasurableSet E := measurableSet_expandingSet h p δ
  change ENNReal.ofReal (1/1000) ≤ phaseGibbs U E
  rw [phaseGibbs_eq_withDensity U hU hi,withDensity_apply _ hE]
  change _ ≤ ∫⁻ z in E, (ENNReal.ofReal Z)⁻¹*ENNReal.ofReal (Real.exp (-phaseEnergy U z)) ∂μ
  have hcompare : (ENNReal.ofReal (Real.exp (-2)/Z))*μ E ≤
      ∫⁻ z in E, (ENNReal.ofReal Z)⁻¹*ENNReal.ofReal (Real.exp (-phaseEnergy U z)) ∂μ := by
    rw [← Measure.restrict_apply_univ,← lintegral_const]
    apply lintegral_mono_ae
    apply (ae_restrict_iff' hE).mpr
    refine ae_of_all _ (fun z hz => ?_)
    rw [ENNReal.ofReal_div_of_pos hZ,div_eq_mul_inv,mul_comm]
    gcongr
    exact (show phaseEnergy U z < 2 from expandingSet_energy_upper hh hh₁ hδ hδp hz).le
  apply le_trans _ hcompare
  rw [show μ E = ENNReal.ofReal (3*(cycleLength p:ℝ)*h/200) from expandingSet_volume hh hp hδ hδp,
    ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  apply qstar_numeric.trans
  have hvol : 9*Real.pi/100 ≤ 3*(cycleLength p:ℝ)*h/200 := by
    unfold cycleLength
    push_cast
    linarith only [hph]
  have hratio : 9/1200 ≤ (3*(cycleLength p:ℝ)*h/200)/Z := by
    apply (le_div_iff₀ hZ).mpr
    linarith only [hvol,hZu]
  have hm := mul_le_mul_of_nonneg_right hratio (Real.exp_nonneg (-2))
  convert hm using 1 <;> ring

end BreakingResonance

#print axioms BreakingResonance.fastPotential_normalizer
#print axioms BreakingResonance.fastPhase_normalizer_bound
#print axioms BreakingResonance.expandingSet_gibbs_probability
