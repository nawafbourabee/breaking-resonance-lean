import BreakingResonance.AcceptedExit
import PersistencePays.ConditionalLawEntropy

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory Set

namespace BreakingResonance

variable {S : Type*} [MeasurableSpace S]

/-- The two-cell relative entropy bound is weakest at target mass one half
in the exit-probability range used in Lemma 6.9. -/
theorem binary_log_lower_general {x r θ : ℝ} (hx : 0 < x) (hx₁ : x ≤ 1/2)
    (hr : 0 ≤ r) (hr₁ : r ≤ (1-θ)/2) :
    (1-θ-r)*Real.log (1/x)+r*Real.log (1/(1-x)) ≥ (1-θ)*Real.log 2 := by
  have hx1 : 0<1-x := by linarith
  have hprod : x*(1-x)≤1/4 := by nlinarith [sq_nonneg (x-1/2)]
  have hl1 : Real.log 2≤Real.log (1/x) := by
    apply Real.log_le_log (by norm_num)
    exact (le_div_iff₀ hx).mpr (by linarith)
  have hl2 : 2*Real.log 2≤Real.log (1/x)+Real.log (1/(1-x)) := by
    have hh : Real.log (4:ℝ)≤Real.log (1/(x*(1-x))) := by
      apply Real.log_le_log (by norm_num)
      exact (le_div_iff₀ (mul_pos hx hx1)).mpr (by linarith)
    have h4 : Real.log (4:ℝ)=2*Real.log 2 := by
      have hh := Real.log_pow (2:ℝ) 2
      norm_num at hh
      exact hh
    rw [h4] at hh
    simpa only [one_div,Real.log_inv,Real.log_mul hx.ne' hx1.ne',neg_add_rev,add_comm] using hh
  have h1 := mul_le_mul_of_nonneg_left hl1 (show 0 ≤ 1-θ-2*r by linarith only [hr₁])
  have h2 := mul_le_mul_of_nonneg_left hl2 hr
  nlinarith only [h1,h2]

theorem entropy_forces_exit_general (μ π : Measure S)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure π]
    (hK : klDiv μ π ≠ ⊤) (A : Set S) (hA : MeasurableSet A)
    (hApos : 0 < π.real A) (hAmax : π.real A ≤ 1/2)
    {θ φ₀ e₀ : ℝ} (hθ : 0 ≤ θ) (hφ₀ : 0 < φ₀) (hφθ : φ₀ ≤ (1-θ)/2)
    (hE : (klDiv μ π).toReal ≤ θ*Real.log (1/π.real A)+e₀)
    (hthreshold : Real.binEntropy φ₀+e₀ ≤ (1-θ)*Real.log 2) :
    φ₀ ≤ μ.real Aᶜ := by
  by_contra! hlt
  have hp0 : 0 ≤ μ.real Aᶜ := ENNReal.toReal_nonneg
  have hbin := binary_partition_entropy μ π hK A hA hApos (by linarith)
  have hl := binary_log_lower_general hApos hAmax hp0 (hlt.le.trans hφθ)
  have hmono := Real.binEntropy_strictMonoOn
    (show μ.real Aᶜ ∈ Icc 0 ((2:ℝ)⁻¹) from ⟨hp0,by linarith only [hlt,hφθ,hθ]⟩)
    (show φ₀ ∈ Icc 0 ((2:ℝ)⁻¹) from ⟨hφ₀.le,by linarith only [hφθ,hθ]⟩) hlt
  nlinarith only [hbin,hl,hmono,hE,hthreshold]

end BreakingResonance

#print axioms BreakingResonance.entropy_forces_exit_general
