import BreakingResonance.Reversibility
import BreakingResonance.EntropyExit

/-! Accepted exits under a conditioned stationary initial law. -/
noncomputable section
namespace BreakingResonance
open PersistencePays MeasureTheory ProbabilityTheory InformationTheory Set
open scoped ENNReal
variable {S V : Type*} [MeasurableSpace S] [MeasurableSpace V]

theorem accepted_exit_from_conditioning
    (Q : S×V → S) (hQ : Measurable Q) (G : S×V → ℝ) (hG : Measurable G)
    (π : Measure S) [IsProbabilityMeasure π] (ν : Measure V) [IsProbabilityMeasure ν]
    (A : Set S) (hA : MeasurableSet A) (E : Set (S×V)) (hE : MeasurableSet E)
    (hEA : E ⊆ Prod.fst ⁻¹' A) (α : ℝ≥0∞)
    (hα : ∀z∈E,α≤acceptProbability G z) :
    α*(π.prod ν) E*((cond (π.prod ν) E).map Q) Aᶜ ≤
      ∫⁻x in A,proposalKernel Q hQ G hG ν x Aᶜ ∂π := by
  rw [proposalKernel_flow_integral Q hQ G hG ν π A Aᶜ hA hA.compl]
  have he : (π.prod ν) E*((cond (π.prod ν) E).map Q) Aᶜ=
      (π.prod ν) (E∩Q ⁻¹' Aᶜ) := by
    rw [Measure.map_apply hQ hA.compl,mul_comm]
    exact cond_mul_eq_inter hE _ _
  rw [mul_assoc α,he]
  have hint : α*(π.prod ν) (E∩Q ⁻¹' Aᶜ)=
      ∫⁻z in E,α*Aᶜ.indicator (fun _ : S=>(1:ℝ≥0∞)) (Q z) ∂π.prod ν := by
    have heq : (fun z : S×V=>Aᶜ.indicator (fun _ : S=>(1:ℝ≥0∞)) (Q z))=
        (Q ⁻¹' Aᶜ).indicator (fun _ =>(1:ℝ≥0∞)) := by
      rfl
    rw [lintegral_const_mul α (show Measurable (fun z : S×V=>Aᶜ.indicator (fun _ : S=>(1:ℝ≥0∞)) (Q z)) from
      (measurable_const.indicator hA.compl).comp hQ),heq,
      lintegral_indicator (hA.compl.preimage hQ)]
    simp only [lintegral_const,Measure.restrict_apply_univ,Measure.restrict_apply (hA.compl.preimage hQ),
      one_mul,Set.inter_comm]
  rw [hint]
  calc
    _≤∫⁻z in E,A.indicator (fun _ : S=>(1:ℝ≥0∞)) z.1*
        metropolisDecisionKernel Q hQ G hG z Aᶜ ∂π.prod ν := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hE] with z hz
      have hza : z.1∈A := hEA hz
      simp only [indicator_of_mem hza,one_mul,metropolisDecisionKernel,Kernel.coe_mk,
        Measure.add_apply,Measure.smul_apply,smul_eq_mul,Measure.dirac_apply' _ hA.compl]
      change α*Aᶜ.indicator (fun _=>(1:ℝ≥0∞)) (Q z)≤
        acceptProbability G z*Aᶜ.indicator (fun _=>1) (Q z)+_
      exact (mul_le_mul' (hα z hz) le_rfl).trans (le_add_right le_rfl)
    _≤_ := lintegral_mono' Measure.restrict_le_self le_rfl

theorem conditional_entropy_upper {η p b : ℝ} (hη : 0<η) (hη1 : η<1)
    (hp : 0<p) (hb : (1-η)*p≤b) :
    -Real.log b≤Real.log (1/p)+η/(1-η) := by
  have hd : 0<1-η := by linarith
  have hl := Real.log_le_log (mul_pos hd hp) hb
  rw [Real.log_mul hd.ne' hp.ne'] at hl
  have he := Real.log_le_sub_one_of_pos (inv_pos.mpr hd)
  rw [Real.log_inv] at he
  have hi : (1-η)⁻¹-1=η/(1-η) := by field_simp; ring
  rw [hi] at he
  simp only [one_div,Real.log_inv]
  linarith

theorem conditioned_entropy_forces_exit
    (μ π : Measure S) [IsProbabilityMeasure μ] [IsProbabilityMeasure π]
    (hK : klDiv μ π≠∞) (A : Set S) (hA : MeasurableSet A)
    (hApos : 0<π.real A) (hAmax : π.real A≤1/2)
    {η b : ℝ} (hη : 0<η) (hηmax : η≤1/600)
    (hb : (1-η)*π.real A≤b)
    (hE : (klDiv μ π).toReal≤(41:ℝ)/48*(-Real.log b)+49*η/72) :
    1/(50*(1-η)^2)≤μ.real Aᶜ := by
  apply entropy_forces_exit μ π hK A hA hApos hAmax hη hηmax
  have hb' := conditional_entropy_upper hη (by linarith : η<1) hApos hb
  have hh := mul_le_mul_of_nonneg_left hb' (by norm_num : (0:ℝ)≤41/48)
  have he : (41:ℝ)/48*(η/(1-η))=41*η/(48*(1-η)) := by simp only [div_eq_mul_inv,mul_inv_rev]; ring
  rw [mul_add,he] at hh
  linarith

end BreakingResonance
