import BreakingResonance.AcceptedExit

/-! Restricted conductance from proposal entropy and acceptance on an energy set. -/
noncomputable section
namespace BreakingResonance
open PersistencePays MeasureTheory ProbabilityTheory InformationTheory Set
open scoped ENNReal
variable {S V : Type*} [MeasurableSpace S] [MeasurableSpace V]

theorem entropy_conductance
    (Q : S×V → S) (hQ : Measurable Q) (G : S×V → ℝ) (hG : Measurable G)
    (π : Measure S) [IsProbabilityMeasure π] (ν : Measure V) [IsProbabilityMeasure ν]
    (A : Set S) (hA : MeasurableSet A) (E : Set (S×V)) (hE : MeasurableSet E)
    (hEA : E ⊆ Prod.fst ⁻¹' A) (hApos : 0<π.real A) (hAmax : π.real A≤1/2)
    {η : ℝ} (hη : 0<η) (hηmax : η≤1/600)
    (hmass : (1-η)*π.real A≤(π.prod ν).real E)
    (hacc : ∀z∈E,ENNReal.ofReal (1-η)≤acceptProbability G z)
    (hfinite : klDiv ((cond (π.prod ν) E).map Q) π≠∞)
    (hentropy : (klDiv ((cond (π.prod ν) E).map Q) π).toReal≤
      (41:ℝ)/48*(-Real.log ((π.prod ν).real E))+49*η/72) :
    π.real A/50≤(∫⁻x in A,proposalKernel Q hQ G hG ν x Aᶜ ∂π).toReal := by
  have hd : 0<1-η := by linarith
  have hmasspos : 0<(π.prod ν).real E := (mul_pos hd hApos).trans_le hmass
  have hEpos : (π.prod ν) E≠0 := by
    intro he
    change 0<((π.prod ν) E).toReal at hmasspos
    simp [he] at hmasspos
  letI : IsProbabilityMeasure (cond (π.prod ν) E) := cond_isProbabilityMeasure hEpos
  let μ := (cond (π.prod ν) E).map Q
  letI : IsProbabilityMeasure μ := Measure.isProbabilityMeasure_map hQ.aemeasurable
  have hexit : 1/(50*(1-η)^2)≤μ.real Aᶜ :=
    conditioned_entropy_forces_exit μ π hfinite A hA hApos hAmax hη hηmax hmass hentropy
  have hf := accepted_exit_from_conditioning Q hQ G hG π ν A hA E hE hEA
    (ENNReal.ofReal (1-η)) hacc
  have hflow : (∫⁻x in A,proposalKernel Q hQ G hG ν x Aᶜ ∂π)≤π A := by
    calc
      _≤∫⁻_ in A,(1:ℝ≥0∞) ∂π :=
        lintegral_mono (fun x=>prob_le_one)
      _=π A := by simp
  have ht := ENNReal.toReal_mono (ne_top_of_le_ne_top (measure_ne_top π A) hflow) hf
  rw [ENNReal.toReal_mul,ENNReal.toReal_mul,ENNReal.toReal_ofReal hd.le] at ht
  change (1-η)*(π.prod ν).real E*μ.real Aᶜ≤_ at ht
  have hm := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hmass hd.le) (show 0≤μ.real Aᶜ from ENNReal.toReal_nonneg)
  have he := mul_le_mul_of_nonneg_left hexit
    (mul_nonneg hd.le (mul_nonneg hd.le hApos.le))
  have hid : (1-η)*((1-η)*π.real A)*(1/(50*(1-η)^2))=π.real A/50 := by
    field_simp
    <;> ring
  rw [hid] at he
  exact he.trans (hm.trans ht)

end BreakingResonance
