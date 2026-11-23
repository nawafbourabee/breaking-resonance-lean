import BreakingResonance.MetropolisFlow
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Density level integrals for the accepted part of the kernel in Lemma 5.2. -/
noncomputable section
namespace BreakingResonance
open MeasureTheory Set
open scoped ENNReal

theorem acceptedWeight_lintegral_levels {S : Type*}
    (p : S → ℝ≥0∞) (hp : ∀ z, p z ≠ ∞) (T : S → S) (z : S) :
    (∫⁻ u : ℝ, (Ioc 0 (p z).toReal).indicator 1 u *
      (Ioc 0 (p (T z)).toReal).indicator 1 u) = acceptedWeight p T z := by
  have h (u : ℝ) :
      (Ioc 0 (p z).toReal).indicator (1 : ℝ → ℝ≥0∞) u *
        (Ioc 0 (p (T z)).toReal).indicator (1 : ℝ → ℝ≥0∞) u =
      (Ioc 0 (min (p z) (p (T z))).toReal).indicator (1 : ℝ → ℝ≥0∞) u := by
    have hmin : u ∈ Ioc 0 (min (p z) (p (T z))).toReal ↔
        u ∈ Ioc 0 (p z).toReal ∧ u ∈ Ioc 0 (p (T z)).toReal := by
      rw [ENNReal.toReal_min (hp z) (hp (T z))]
      simp only [mem_Ioc, le_min_iff]
      tauto
    by_cases hz : u ∈ Ioc 0 (p z).toReal <;>
      by_cases hT : u ∈ Ioc 0 (p (T z)).toReal <;>
      simp [indicator, hmin, hz, hT]
  simp_rw [h]
  rw [lintegral_indicator_one measurableSet_Ioc, Real.volume_Ioc, sub_zero,
    ENNReal.ofReal_toReal ((min_le_left _ _).trans_lt (lt_top_iff_ne_top.mpr (hp z))).ne]
  rfl

theorem lintegral_acceptedWeight_levels {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [SFinite μ] (p : S → ℝ≥0∞) (hp : ∀ z, p z ≠ ∞)
    (hpm : Measurable p) (T : S → S) (hTm : Measurable T)
    (F : S → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ u : ℝ, ∫⁻ z, (Ioc 0 (p z).toReal).indicator 1 u *
      (Ioc 0 (p (T z)).toReal).indicator 1 u * F z ∂μ) =
    ∫⁻ z, acceptedWeight p T z * F z ∂μ := by
  let g : ℝ → S → ℝ≥0∞ := fun u z =>
    (Ioc 0 (p z).toReal).indicator 1 u *
      (Ioc 0 (p (T z)).toReal).indicator 1 u * F z
  have hlevel (d : S → ℝ≥0∞) (hd : Measurable d) :
      Measurable (fun x : ℝ × S => (Ioc 0 (d x.2).toReal).indicator
        (1 : ℝ → ℝ≥0∞) x.1) := by
    have hs : MeasurableSet {x : ℝ × S | 0 < x.1 ∧ x.1 ≤ (d x.2).toReal} :=
      (measurableSet_lt measurable_const measurable_fst).inter
        (measurableSet_le measurable_fst (hd.ennreal_toReal.comp measurable_snd))
    have he : (fun x : ℝ × S => (Ioc 0 (d x.2).toReal).indicator
        (1 : ℝ → ℝ≥0∞) x.1) =
        ({x : ℝ × S | 0 < x.1 ∧ x.1 ≤ (d x.2).toReal}).indicator 1 := by
      funext x
      rfl
    rw [he]
    exact measurable_const.indicator hs
  have hg : Measurable (Function.uncurry g) :=
    ((hlevel p hpm).mul (hlevel (p ∘ T) (hpm.comp hTm))).mul (hF.comp measurable_snd)
  change (∫⁻ u : ℝ, ∫⁻ z, g u z ∂μ) = _
  rw [lintegral_lintegral_swap hg.aemeasurable]
  apply lintegral_congr
  intro z
  dsimp only [g]
  have hm : Measurable (fun u : ℝ => (Ioc 0 (p z).toReal).indicator (1 : ℝ → ℝ≥0∞) u *
      (Ioc 0 (p (T z)).toReal).indicator (1 : ℝ → ℝ≥0∞) u) :=
    (measurable_const.indicator measurableSet_Ioc).mul
      (measurable_const.indicator measurableSet_Ioc)
  rw [lintegral_mul_const _ hm, acceptedWeight_lintegral_levels p hp T z]

/-- Signed version of the accepted-weight identity for an integrable
product of the two test-function values in Lemma 5.2. -/
theorem integrable_integral_acceptedWeight_levels {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [SFinite μ] (p : S → ℝ≥0∞) (hp : ∀ z, p z ≠ ∞)
    (hpm : Measurable p) (T : S → S) (hTm : Measurable T)
    (F : S → ℝ) (hF : Measurable F)
    (hi : Integrable (fun z => (acceptedWeight p T z).toReal * F z) μ) :
    Integrable (fun u : ℝ => ∫ z, (Ioc 0 (p z).toReal).indicator (1 : ℝ → ℝ) u *
      (Ioc 0 (p (T z)).toReal).indicator (1 : ℝ → ℝ) u * F z ∂μ) ∧
    (∫ u : ℝ, ∫ z, (Ioc 0 (p z).toReal).indicator (1 : ℝ → ℝ) u *
      (Ioc 0 (p (T z)).toReal).indicator (1 : ℝ → ℝ) u * F z ∂μ) =
    ∫ z, (acceptedWeight p T z).toReal * F z ∂μ := by
  let a := acceptedWeight p T
  have ha : Measurable a := hpm.min (hpm.comp hTm)
  have ha₀ (z : S) : a z ≠ ∞ :=
    ((min_le_left (p z) (p (T z))).trans_lt (lt_top_iff_ne_top.mpr (hp z))).ne
  let G := fun (u : ℝ) (z : S) => (Ioc 0 (a z).toReal).indicator (fun _ => F z) u
  have hG (u : ℝ) (z : S) :
      (Ioc 0 (p z).toReal).indicator (1 : ℝ → ℝ) u *
        (Ioc 0 (p (T z)).toReal).indicator (1 : ℝ → ℝ) u * F z = G u z := by
    have hmin : u ∈ Ioc 0 (a z).toReal ↔
        u ∈ Ioc 0 (p z).toReal ∧ u ∈ Ioc 0 (p (T z)).toReal := by
      dsimp only [a, acceptedWeight]
      rw [ENNReal.toReal_min (hp z) (hp (T z))]
      simp only [mem_Ioc, le_min_iff]
      tauto
    by_cases ha : u ∈ Ioc 0 (a z).toReal
    · obtain ⟨hz, hT⟩ := hmin.mp ha
      simp only [G, indicator_of_mem ha, indicator_of_mem hz, indicator_of_mem hT,
        Pi.one_apply, one_mul]
    · by_cases hz : u ∈ Ioc 0 (p z).toReal
      · have hT : u ∉ Ioc 0 (p (T z)).toReal := fun hT => ha (hmin.mpr ⟨hz,hT⟩)
        simp only [G, indicator_of_notMem ha, indicator_of_notMem hT, mul_zero, zero_mul]
      · simp only [G, indicator_of_notMem ha, indicator_of_notMem hz, zero_mul]
  have hmeas : Measurable (Function.uncurry G) := by
    change Measurable ({x : ℝ × S | 0 < x.1 ∧ x.1 ≤ (a x.2).toReal}.indicator (F ∘ Prod.snd))
    exact (hF.comp measurable_snd).indicator
      ((measurableSet_lt measurable_const measurable_fst).inter
        (measurableSet_le measurable_fst (ha.ennreal_toReal.comp measurable_snd)))
  have hGi : Integrable (Function.uncurry G) ((volume : Measure ℝ).prod μ) := by
    refine ⟨hmeas.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm,
      lintegral_prod_symm _ hmeas.enorm.aemeasurable]
    have hinner (z : S) : (∫⁻ u : ℝ, ‖G u z‖ₑ) = ‖(a z).toReal * F z‖ₑ := by
      have he (u : ℝ) : ‖G u z‖ₑ =
          (Ioc 0 (a z).toReal).indicator (fun _ => ‖F z‖ₑ) u := by
        by_cases hu : u ∈ Ioc 0 (a z).toReal
        · simp only [G, indicator_of_mem hu]
        · simp only [G, indicator_of_notMem hu, enorm_zero]
      simp_rw [he]
      rw [lintegral_indicator measurableSet_Ioc, lintegral_const, Measure.restrict_apply_univ,
        Real.volume_Ioc, sub_zero, ENNReal.ofReal_toReal (ha₀ z), enorm_mul]
      have ha' : ‖(a z).toReal‖ₑ = a z := by
        rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg ENNReal.toReal_nonneg,
          ENNReal.ofReal_toReal (ha₀ z)]
      rw [ha', mul_comm]
    change (∫⁻ z, ∫⁻ u : ℝ, ‖G u z‖ₑ ∂volume ∂μ) < ∞
    simp_rw [hinner]
    exact hasFiniteIntegral_iff_enorm.mp hi.2
  simp_rw [hG]
  refine ⟨hGi.integral_prod_left, ?_⟩
  rw [integral_integral_swap hGi]
  apply integral_congr_ae
  filter_upwards with z
  dsimp only [G]
  rw [integral_indicator_const (F z) measurableSet_Ioc, measureReal_def,
    Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal ENNReal.toReal_nonneg, smul_eq_mul]

theorem integral_acceptedWeight_levels {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [SFinite μ] (p : S → ℝ≥0∞) (hp : ∀ z, p z ≠ ∞)
    (hpm : Measurable p) (T : S → S) (hTm : Measurable T)
    (F : S → ℝ) (hF : Measurable F)
    (hi : Integrable (fun z => (acceptedWeight p T z).toReal * F z) μ) :
    (∫ u : ℝ, ∫ z, (Ioc 0 (p z).toReal).indicator (1 : ℝ → ℝ) u *
      (Ioc 0 (p (T z)).toReal).indicator (1 : ℝ → ℝ) u * F z ∂μ) =
    ∫ z, (acceptedWeight p T z).toReal * F z ∂μ :=
  (integrable_integral_acceptedWeight_levels μ p hp hpm T hTm F hF hi).2

/-- Cutting off at a positive density level turns a square-integrable
function for the weighted measure into one for the original measure. -/
theorem densityLevel_memLp {S : Type*} [MeasurableSpace S] (μ : Measure S)
    (p : S → ℝ≥0∞) (hp : ∀ z, p z ≠ ∞) (hpm : Measurable p)
    (f : S → ℝ) (hfm : Measurable f) (hf : MemLp f 2 (μ.withDensity p))
    {u : ℝ} (hu : 0 < u) :
    MemLp ({z | u ≤ (p z).toReal}.indicator f) 2 μ := by
  let D := {z | u ≤ (p z).toReal}
  have hD : MeasurableSet D := measurableSet_le measurable_const hpm.ennreal_toReal
  have hsq : Integrable (fun z => f z ^ 2) (μ.withDensity p) :=
    (memLp_two_iff_integrable_sq hfm.aestronglyMeasurable).mp hf
  have hw : Integrable (fun z => (p z).toReal * f z ^ 2) μ :=
    (integrable_withDensity_iff_integrable_smul' hpm
      (Filter.Eventually.of_forall fun z => lt_top_iff_ne_top.mpr (hp z))).mp hsq
  apply (memLp_two_iff_integrable_sq (hfm.indicator hD).aestronglyMeasurable).mpr
  apply (hw.const_mul (1/u)).mono' ((hfm.indicator hD).pow_const 2).aestronglyMeasurable
  filter_upwards with z
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  by_cases hz : z ∈ D
  · rw [indicator_of_mem hz]
    have hz' : u ≤ (p z).toReal := hz
    have h := mul_le_mul_of_nonneg_right hz' (sq_nonneg (f z))
    rw [one_div_mul_eq_div]
    exact (le_div_iff₀ hu).mpr (by simpa only [mul_comm (f z ^ 2) u] using h)
  · rw [indicator_of_notMem hz, zero_pow (by decide : (2 : ℕ) ≠ 0)]
    positivity

/-- Absolute integrability of the accepted quadratic form in Lemma 5.2,
using each of the two bounds on the accepted density. -/
theorem acceptedWeight_integrable_product {S : Type*} [MeasurableSpace S]
    (μ : Measure S) (p : S → ℝ≥0∞) (hp : ∀ z, p z ≠ ∞) (hpm : Measurable p)
    (T : S → S) (hT : MeasurePreserving T μ μ)
    (f : S → ℝ) (hfm : Measurable f) (hf : MemLp f 2 (μ.withDensity p)) :
    Integrable (fun z => (acceptedWeight p T z).toReal * (f z * f (T z))) μ := by
  let a := acceptedWeight p T
  have ham : Measurable a := hpm.min (hpm.comp hT.measurable)
  have hsq : Integrable (fun z => f z ^ 2) (μ.withDensity p) :=
    (memLp_two_iff_integrable_sq hfm.aestronglyMeasurable).mp hf
  have hw : Integrable (fun z => (p z).toReal * f z ^ 2) μ :=
    (integrable_withDensity_iff_integrable_smul' hpm
      (Filter.Eventually.of_forall fun z => lt_top_iff_ne_top.mpr (hp z))).mp hsq
  have hsum := (hw.add (hT.integrable_comp_of_integrable hw)).const_mul (1/2 : ℝ)
  refine hsum.mono' ((ham.ennreal_toReal.mul (hfm.mul (hfm.comp hT.measurable))).aestronglyMeasurable) ?_
  filter_upwards with z
  simp only [Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (ENNReal.toReal_nonneg (a := acceptedWeight p T z)),
    Pi.add_apply, Function.comp_apply]
  have haLeft : (a z).toReal ≤ (p z).toReal :=
    ENNReal.toReal_mono (hp z) (min_le_left _ _)
  have haRight : (a z).toReal ≤ (p (T z)).toReal :=
    ENNReal.toReal_mono (hp (T z)) (min_le_right _ _)
  have hLeft := mul_le_mul_of_nonneg_right haLeft (sq_nonneg (f z))
  have hRight := mul_le_mul_of_nonneg_right haRight (sq_nonneg (f (T z)))
  have hcross : 2 * (|f z| * |f (T z)|) ≤ f z^2 + f (T z)^2 := by
    nlinarith only [sq_nonneg (|f z| - |f (T z)|), sq_abs (f z), sq_abs (f (T z))]
  have habs := mul_le_mul_of_nonneg_left hcross (ENNReal.toReal_nonneg (a := a z))
  nlinarith only [hLeft,hRight,habs]

/-- The integral of the squared norm over density levels. This is the
normalization used with the Fourier inequalities in Lemma 5.2. -/
theorem integrable_integral_densityLevel_sq {S : Type*} [MeasurableSpace S] (μ : Measure S)
    [SFinite μ] (p : S → ℝ≥0∞) (hp : ∀ z, p z ≠ ∞) (hpm : Measurable p)
    (f : S → ℝ) (hfm : Measurable f) (hf : MemLp f 2 (μ.withDensity p)) :
    Integrable (fun u : ℝ => ∫ z, (Ioc 0 (p z).toReal).indicator (fun _ => f z) u ^ 2 ∂μ) ∧
    (∫ u : ℝ, ∫ z, (Ioc 0 (p z).toReal).indicator (fun _ => f z) u ^ 2 ∂μ) =
      ∫ z, f z ^ 2 ∂μ.withDensity p := by
  have ha : acceptedWeight p id = p := by
    funext z
    simp [acceptedWeight]
  have hf₂ := (memLp_two_iff_integrable_sq hfm.aestronglyMeasurable).mp hf
  have hp₀ : ∀ᵐ z ∂μ, p z < ∞ :=
    Filter.Eventually.of_forall (fun z => lt_top_iff_ne_top.mpr (hp z))
  have hw : Integrable (fun z => (acceptedWeight p id z).toReal * f z ^ 2) μ := by
    rw [ha]
    exact (integrable_withDensity_iff_integrable_smul' hpm hp₀).mp hf₂
  have he := integrable_integral_acceptedWeight_levels μ p hp hpm id measurable_id
    (fun z => f z^2) (hfm.pow_const 2) hw
  rw [ha] at he
  simp only [id_eq] at he
  have he' (u : ℝ) (z : S) :
      (Ioc 0 (p z).toReal).indicator (1 : ℝ → ℝ) u *
        (Ioc 0 (p z).toReal).indicator (1 : ℝ → ℝ) u * f z^2 =
      ((Ioc 0 (p z).toReal).indicator (fun _ => f z) u)^2 := by
    by_cases hu : u ∈ Ioc 0 (p z).toReal
    · simp only [indicator_of_mem hu, Pi.one_apply, one_mul]
    · simp only [indicator_of_notMem hu, zero_mul, zero_pow (by decide : (2 : ℕ) ≠ 0)]
  simp_rw [he'] at he
  rw [integral_withDensity_eq_integral_toReal_smul hpm hp₀]
  exact he

theorem integral_densityLevel_sq {S : Type*} [MeasurableSpace S] (μ : Measure S)
    [SFinite μ] (p : S → ℝ≥0∞) (hp : ∀ z, p z ≠ ∞) (hpm : Measurable p)
    (f : S → ℝ) (hfm : Measurable f) (hf : MemLp f 2 (μ.withDensity p)) :
    (∫ u : ℝ, ∫ z, (Ioc 0 (p z).toReal).indicator (fun _ => f z) u ^ 2 ∂μ) =
      ∫ z, f z ^ 2 ∂μ.withDensity p :=
  (integrable_integral_densityLevel_sq μ p hp hpm f hfm hf).2

end BreakingResonance

#print axioms BreakingResonance.acceptedWeight_lintegral_levels
#print axioms BreakingResonance.lintegral_acceptedWeight_levels

#print axioms BreakingResonance.densityLevel_memLp

#print axioms BreakingResonance.integral_acceptedWeight_levels
#print axioms BreakingResonance.integrable_integral_acceptedWeight_levels
#print axioms BreakingResonance.integrable_integral_densityLevel_sq
