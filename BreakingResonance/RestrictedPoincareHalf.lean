import BreakingResonance.RestrictedLevelSets

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ProbabilityTheory ENNReal

namespace BreakingResonance

variable {S : Type*} [MeasurableSpace S]

/-- The energy calculation after disintegrating over upper level sets. -/
theorem restrictedConductance_half_square
    (π : Measure S) [IsProbabilityMeasure π] (P : Kernel S S) [IsMarkovKernel P]
    (hrev : P.IsReversible π) {s φ C : ℝ} (hs : 0 ≤ s) (hφ : 0 < φ)
    (hcond : RestrictedConductance π P s φ) {g : S → ℝ} (hg : Measurable g)
    (hlo : ∀ x, 0 ≤ g x) (hhi : ∀ x, g x ≤ C)
    (hsupport : π {x | 0 < g x} ≤ 1/2) :
    (∫ x, (g x)^2 ∂π) ≤ 2/φ^2 * markovDirichlet π P g + 2*s*C^2 := by
  let ν := π ⊗ₘ P
  have hfst : MeasurePreserving Prod.fst ν π := ⟨measurable_fst, Measure.fst_compProd π P⟩
  have hsnd : MeasurePreserving Prod.snd ν π := kernel_snd_measurePreserving π P hrev.invariant
  have hswap : MeasurePreserving Prod.swap ν ν :=
    ⟨measurable_swap, reversible_compProd_map_swap π P hrev⟩
  let a (x : S) := (g x)^2
  have ha : Measurable a := hg.pow_const 2
  have hab (x : S) : a x ≤ C^2 := (sq_le_sq₀ (hlo x) ((hlo x).trans (hhi x))).mpr (hhi x)
  have ha₀ (x : S) : 0 ≤ a x := sq_nonneg _
  have hia : Integrable a π := (memLp_of_bounded
    (Filter.Eventually.of_forall fun x => ⟨ha₀ x,hab x⟩) ha.aestronglyMeasurable 1).integrable le_rfl
  let d (z : S×S) := a z.1-a z.2
  let e (z : S×S) := (g z.1-g z.2)^2
  let pos (z : S×S) := max (d z) 0
  have hapl : Integrable (fun z : S×S => a z.1) ν := hfst.integrable_comp_of_integrable hia
  have hapr : Integrable (fun z : S×S => a z.2) ν := hsnd.integrable_comp_of_integrable hia
  have hd : Integrable d ν := hapl.sub hapr
  have hpos₀ (z : S×S) : 0 ≤ pos z := le_max_right _ _
  have hmeaspos : Measurable pos :=
    ((ha.comp measurable_fst).sub (ha.comp measurable_snd)).max measurable_const
  have hpos : Integrable pos ν := hd.norm.mono'
    hmeaspos.aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hpos₀ z), Real.norm_eq_abs]
      exact max_le (le_abs_self _) (abs_nonneg _))
  have hme : Measurable e := ((hg.comp measurable_fst).sub (hg.comp measurable_snd)).pow_const 2
  have hie : Integrable e ν := (memLp_of_bounded (a := 0) (b := (2*C)^2)
    (Filter.Eventually.of_forall fun z => ⟨sq_nonneg _,by
      have hC : 0 ≤ C := (hlo z.1).trans (hhi z.1)
      have habs : |g z.1-g z.2| ≤ 2*C := abs_le.mpr
        ⟨by linarith only [hlo z.1,hhi z.2,hC],by linarith only [hhi z.1,hlo z.2,hC]⟩
      simpa [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr habs⟩)
    hme.aestronglyMeasurable 1).integrable le_rfl
  have hsupport' : π {x | 0 < a x} ≤ 1/2 :=
    (measure_mono (fun x hx => lt_of_le_of_ne (hlo x)
      (Ne.symm (fun hn => (ne_of_gt (show 0 < a x from hx)) (by simp [a,hn]))))).trans hsupport
  have hflow := restrictedConductance_crossing_bound π P hcond (sq_nonneg C)
    ha ha₀ hab hsupport' 
  change ENNReal.ofReal φ * (∫⁻ x, ENNReal.ofReal (a x) ∂π) ≤
    ENNReal.ofReal φ * ENNReal.ofReal s * ENNReal.ofReal (C^2) +
      ∫⁻ z, ENNReal.ofReal (d z) ∂ν at hflow
  have hlin : (∫⁻ z, ENNReal.ofReal (d z) ∂ν) =
      ∫⁻ z, ENNReal.ofReal (pos z) ∂ν := by
    apply lintegral_congr
    intro z
    by_cases h : 0 ≤ d z
    · simp [pos,max_eq_left h]
    · rw [ENNReal.ofReal_eq_zero.mpr (le_of_not_ge h),show pos z = 0 from max_eq_right (le_of_not_ge h)]
      simp
  rw [hlin, ← ofReal_integral_eq_lintegral_ofReal hia (Filter.Eventually.of_forall ha₀),
    ← ofReal_integral_eq_lintegral_ofReal hpos
      (Filter.Eventually.of_forall hpos₀)] at hflow
  have hreal := ENNReal.toReal_mono (by finiteness) hflow
  rw [ENNReal.toReal_add (by finiteness) (by finiteness),ENNReal.toReal_mul,ENNReal.toReal_mul,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal hφ.le, ENNReal.toReal_ofReal hs,
    ENNReal.toReal_ofReal (sq_nonneg C), ENNReal.toReal_ofReal
      (integral_nonneg ha₀), ENNReal.toReal_ofReal (integral_nonneg hpos₀)] at hreal
  have hflip : (∫ z, pos (Prod.swap z) ∂ν) = ∫ z, pos z ∂ν := by
    convert (integral_map measurable_swap.aemeasurable
      (by rw [hswap.map_eq]; exact hpos.aestronglyMeasurable)).symm using 1
    rw [hswap.map_eq]
  have him : Integrable (fun z => pos (Prod.swap z)) ν := hswap.integrable_comp_of_integrable hpos
  have hpoint (z : S×S) : φ*(pos z+pos (Prod.swap z)) ≤
      e z + φ^2/2*(a z.1+a z.2) := by
    unfold pos d e a
    simp only [Prod.fst_swap,Prod.snd_swap]
    by_cases h : g z.2 ≤ g z.1
    · rw [max_eq_left (sub_nonneg.mpr
        ((sq_le_sq₀ (hlo _) (hlo _)).mpr h)),
        max_eq_right (sub_nonpos.mpr ((sq_le_sq₀ (hlo _) (hlo _)).mpr h))]
      nlinarith only [sq_nonneg (g z.1-g z.2-φ*(g z.1+g z.2)/2),
        mul_nonneg (sq_nonneg φ) (sq_nonneg (g z.1-g z.2))]
    · have h' : g z.1 ≤ g z.2 := le_of_not_ge h
      rw [max_eq_right (sub_nonpos.mpr
        ((sq_le_sq₀ (hlo _) (hlo _)).mpr h')),
        max_eq_left (sub_nonneg.mpr ((sq_le_sq₀ (hlo _) (hlo _)).mpr h'))]
      nlinarith only [sq_nonneg (g z.2-g z.1-φ*(g z.1+g z.2)/2),
        mul_nonneg (sq_nonneg φ) (sq_nonneg (g z.1-g z.2))]
  have hbound := integral_mono ((hpos.add him).const_mul φ)
    (hie.add ((hapl.add hapr).const_mul (φ^2/2))) hpoint
  have hsums : (∫ z : S×S, a z.1 + a z.2 ∂ν) = 2*(∫ x, a x ∂π) := by
    have hleft := integral_map measurable_fst.aemeasurable
      (show AEStronglyMeasurable a (ν.map Prod.fst) from hfst.map_eq.symm ▸ hia.aestronglyMeasurable)
    have hright := integral_map measurable_snd.aemeasurable
      (show AEStronglyMeasurable a (ν.map Prod.snd) from hsnd.map_eq.symm ▸ hia.aestronglyMeasurable)
    rw [hfst.map_eq] at hleft
    rw [hsnd.map_eq] at hright
    calc
      _ = (∫ z : S×S, a z.1 ∂ν) + (∫ z : S×S, a z.2 ∂ν) := integral_add hapl hapr
      _ = _ := by rw [← hleft, ← hright]; ring
  have hsumpos : (∫ z, pos z + pos (Prod.swap z) ∂ν) = 2*(∫ z, pos z ∂ν) := by
    calc
      _ = (∫ z, pos z ∂ν) + (∫ z, pos (Prod.swap z) ∂ν) := integral_add hpos him
      _ = _ := by rw [hflip]; ring
  change (∫ z, φ*(pos z+pos (Prod.swap z)) ∂ν) ≤
    ∫ z, e z+(φ^2/2)*(a z.1+a z.2) ∂ν at hbound
  calc
    _ ≤ 2/φ^2 * ((1/2)*(∫ z, e z ∂ν)) + 2*s*C^2 := by
      have hrs : (∫ z, e z+(φ^2/2)*(a z.1+a z.2) ∂ν) =
          (∫ z, e z ∂ν)+(∫ z, (φ^2/2)*(a z.1+a z.2) ∂ν) :=
        integral_add hie ((hapl.add hapr).const_mul _)
      rw [integral_const_mul,hsumpos,hrs,integral_const_mul,hsums] at hbound
      have hφsq : 0 < φ^2 := by positivity
      have hest : φ^2*((∫ x, a x ∂π)-2*s*C^2) ≤ ∫ z, e z ∂ν := by
        have hm := mul_le_mul_of_nonneg_left hreal (show 0 ≤ 2*φ by positivity)
        nlinarith only [hm,hbound]
      have hdiv : (∫ x, a x ∂π)-2*s*C^2 ≤ (∫ z, e z ∂ν)/φ^2 :=
        (le_div_iff₀ hφsq).mpr (by rw [mul_comm]; exact hest)
      change (∫ x, a x ∂π) ≤ 2/φ^2*((1/2)*(∫ z, e z ∂ν))+2*s*C^2
      rw [show 2/φ^2*((1/2)*(∫ z, e z ∂ν)) = (∫ z, e z ∂ν)/φ^2 by ring]
      linarith only [hdiv]
    _ = _ := rfl

end BreakingResonance

#print axioms BreakingResonance.restrictedConductance_half_square
