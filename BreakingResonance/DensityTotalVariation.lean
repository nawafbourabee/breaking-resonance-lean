import BreakingResonance.ReversibleDensities
import BreakingResonance.RejectionBounds

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ProbabilityTheory ENNReal

namespace BreakingResonance

variable {S : Type*} [MeasurableSpace S]

theorem withDensity_real_eq_setIntegral (π : Measure S) {f : S → ℝ}
    (hi : Integrable f π) (h0 : ∀ x, 0 ≤ f x) {A : Set S} (hA : MeasurableSet A) :
    (π.withDensity (ENNReal.ofReal ∘ f)).real A = ∫ x in A, f x ∂π := by
  rw [Measure.real,withDensity_apply _ hA,integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall h0) hi.integrableOn.aestronglyMeasurable]
  rfl

theorem totalVariation_triangle (μ ν π : Measure S) :
    totalVariation μ π ≤ totalVariation μ ν+totalVariation ν π := by
  refine iSup₂_le fun A hA => ?_
  calc
    ENNReal.ofReal |μ.real A-π.real A| ≤
      ENNReal.ofReal (|μ.real A-ν.real A|+|ν.real A-π.real A|) := by
      apply ENNReal.ofReal_le_ofReal
      rw [← show (μ.real A-ν.real A)+(ν.real A-π.real A) = μ.real A-π.real A by ring]
      exact abs_add_le _ _
    _ = ENNReal.ofReal |μ.real A-ν.real A|+ENNReal.ofReal |ν.real A-π.real A| :=
      ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)
    _ ≤ _ := add_le_add (le_iSup₂_of_le A hA le_rfl) (le_iSup₂_of_le A hA le_rfl)

theorem totalVariation_le_of_common_submeasure
    (μ ν : Measure S) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (ξ : Measure S) (hμ : ξ ≤ μ) (hν : ξ ≤ ν) :
    totalVariation μ ν ≤ ENNReal.ofReal (1-ξ.real univ) := by
  have : IsFiniteMeasure ξ := ⟨(hμ univ).trans_lt (measure_lt_top μ _)⟩
  refine iSup₂_le fun A hA => ENNReal.ofReal_le_ofReal ?_
  have hmA : ξ.real A ≤ μ.real A := ENNReal.toReal_mono (measure_ne_top μ _) (hμ A)
  have hnA : ξ.real A ≤ ν.real A := ENNReal.toReal_mono (measure_ne_top ν _) (hν A)
  have hmAc : ξ.real Aᶜ ≤ μ.real Aᶜ := ENNReal.toReal_mono (measure_ne_top μ _) (hμ Aᶜ)
  have hnAc : ξ.real Aᶜ ≤ ν.real Aᶜ := ENNReal.toReal_mono (measure_ne_top ν _) (hν Aᶜ)
  have hm := measureReal_add_measureReal_compl (μ := μ) hA
  have hn := measureReal_add_measureReal_compl (μ := ν) hA
  have hl := measureReal_add_measureReal_compl (μ := ξ) hA
  rw [probReal_univ] at hm hn
  exact abs_le.mpr ⟨by linarith only [hm,hl,hmA,hnAc,hn],
    by linarith only [hn,hl,hnA,hmAc,hm]⟩

/-- The half factor comes from the zero mean of the centered density. -/
theorem density_totalVariation_le_l1 (π : Measure S) [IsProbabilityMeasure π]
    {f : S → ℝ} (hf : Measurable f) (hi : Integrable f π) (h0 : ∀ x, 0 ≤ f x)
    (hmean : (∫ x, f x ∂π) = 1) :
    totalVariation (π.withDensity (ENNReal.ofReal ∘ f)) π ≤
      ENNReal.ofReal ((1/2)*(∫ x, |f x-1| ∂π)) := by
  let g (x : S) := f x-1
  let p (x : S) := max (g x) 0
  have hg : Integrable g π := hi.sub (integrable_const 1)
  have hgm : Measurable g := hf.sub measurable_const
  have hgmean : (∫ x, g x ∂π) = 0 := by
    unfold g
    rw [integral_sub hi (integrable_const (1:ℝ)),hmean,integral_const,probReal_univ,one_smul,sub_self]
  have ht : (∫ x, p x ∂π) = (1/2)*(∫ x, |g x| ∂π) := by
    have he (x : S) : p x = (1/2)*(g x+|g x|) := by
      by_cases hh : 0 ≤ g x
      · simp [p,max_eq_left hh,abs_of_nonneg hh]
        ring
      · have hh' := le_of_not_ge hh
        simp [p,max_eq_right hh',abs_of_nonpos hh']
    change (∫ x, p x ∂π) = _
    simp_rw [he]
    rw [integral_const_mul,integral_add hg hg.abs,hgmean,zero_add]
  have hp : Integrable p π := hg.norm.mono' (hgm.max measurable_const).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg (show 0 ≤ p x from le_max_right _ _),Real.norm_eq_abs]
      exact max_le (le_abs_self _) (abs_nonneg _))
  refine iSup₂_le fun A hA => ENNReal.ofReal_le_ofReal ?_
  rw [withDensity_real_eq_setIntegral π hi h0 hA]
  have hgi : (∫ x in A, g x ∂π) = (∫ x in A,f x ∂π)-π.real A := by
    unfold g
    rw [integral_sub hi.integrableOn (integrable_const (1:ℝ)), setIntegral_const,smul_eq_mul,mul_one]
  have hupper (B : Set S) (hB : MeasurableSet B) : (∫ x in B, g x ∂π) ≤ ∫ x, p x ∂π := by
    rw [← integral_indicator hB]
    exact integral_mono (hg.indicator hB) hp fun x => by
      by_cases hx : x ∈ B
      · exact (indicator_of_mem hx g).le.trans (le_max_left _ _)
      · exact (indicator_of_notMem hx g).le.trans (le_max_right _ _)
  have hsum : (∫ x in A, g x ∂π)+(∫ x in Aᶜ, g x ∂π) = 0 := by
    rw [integral_add_compl hA hg, hgmean]
  change |(∫ x in A, f x ∂π)-π.real A| ≤ (1/2)*(∫ x, |g x| ∂π)
  rw [← hgi,← ht]
  exact abs_le.mpr ⟨by linarith only [hsum,hupper _ hA.compl],hupper _ hA⟩

theorem density_totalVariation_le_l2 (π : Measure S) [IsProbabilityMeasure π]
    {f : S → ℝ} (hf : Measurable f) (hi : MemLp f 2 π) (h0 : ∀ x, 0 ≤ f x)
    (hmean : (∫ x, f x ∂π) = 1) :
    totalVariation (π.withDensity (ENNReal.ofReal ∘ f)) π ≤
      ENNReal.ofReal ((1/2)*Real.sqrt (∫ x, (f x-1)^2 ∂π)) := by
  have hg : MemLp (fun x => f x-1) 2 π := hi.sub (memLp_const 1)
  have ha := hg.norm
  have hai := ha.integrable (by norm_num)
  have hsq := (memLp_two_iff_integrable_sq ha.aestronglyMeasurable).mp ha
  have hcv : ConvexOn ℝ (univ : Set ℝ) (fun t : ℝ => t^2) :=
    (by decide : Even (2 : ℕ)).convexOn_pow
  have hj := hcv.map_integral_le (continuous_id.pow 2).continuousOn isClosed_univ
    (Filter.Eventually.of_forall fun _ => mem_univ _) hai hsq
  simp only [Real.norm_eq_abs,sq_abs] at hj
  have hs := (Real.le_sqrt (integral_nonneg fun _ => abs_nonneg _)
    (integral_nonneg fun _ => sq_nonneg _)).mpr hj
  exact (density_totalVariation_le_l1 π hf (hi.integrable (by norm_num)) h0 hmean).trans
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hs (by norm_num)))

end BreakingResonance

#print axioms BreakingResonance.totalVariation_le_of_common_submeasure
#print axioms BreakingResonance.density_totalVariation_le_l2
