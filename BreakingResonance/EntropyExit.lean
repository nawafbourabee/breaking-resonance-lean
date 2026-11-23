import BreakingResonance.BinaryKL
import BreakingResonance.ConductanceNumerics

/-! The exit probability forced by the proposal entropy estimate. -/
noncomputable section
namespace BreakingResonance
open MeasureTheory ProbabilityTheory InformationTheory Set
open scoped ENNReal
variable {S : Type*} [MeasurableSpace S]

theorem binary_log_lower {x p : ℝ} (hx : 0<x) (hx' : x≤1/2)
    (hp : 0≤p) (hp' : p≤7/96) :
    (7/48-p)*Real.log (1/x)+p*Real.log (1/(1-x))≥(7:ℝ)/48*Real.log 2 := by
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
      have := Real.log_pow (2:ℝ) 2
      norm_num at this
      exact this
    rw [h4] at hh
    simpa only [one_div,Real.log_inv,
      Real.log_mul hx.ne' hx1.ne',neg_add_rev,add_comm] using hh
  have h1 := mul_le_mul_of_nonneg_left hl1 (by linarith : 0≤(7:ℝ)/48-2*p)
  have h2 := mul_le_mul_of_nonneg_left hl2 hp
  nlinarith

theorem entropy_forces_exit (μ π : Measure S)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure π]
    (hK : klDiv μ π≠∞) (A : Set S) (hA : MeasurableSet A)
    (hApos : 0<π.real A) (hAmax : π.real A≤1/2)
    {η : ℝ} (hη : 0<η) (hηmax : η≤1/600)
    (hE : (klDiv μ π).toReal≤(41:ℝ)/48*Real.log (1/π.real A)+
      41*η/(48*(1-η))+49*η/72) :
    1/(50*(1-η)^2)≤μ.real Aᶜ := by
  by_contra hn
  have hp : μ.real Aᶜ<1/(50*(1-η)^2) := lt_of_not_ge hn
  have hd : 0<1-η := by linarith
  have hq : 1/(50*(1-η)^2)≤(7200:ℝ)/358801 := by
    apply (div_le_iff₀ (by positivity : 0<50*(1-η)^2)).mpr
    nlinarith [sq_nonneg (η-1/600)]
  have hp0 : 0≤μ.real Aᶜ := ENNReal.toReal_nonneg
  have hbin := binary_partition_entropy μ π hK A hA hApos (by linarith)
  have hl := binary_log_lower hApos hAmax hp0 (by linarith : μ.real Aᶜ≤7/96)
  have hm := Real.binEntropy_strictMonoOn.monotoneOn
    (show μ.real Aᶜ∈Icc 0 ((2:ℝ)⁻¹) from ⟨hp0,by linarith⟩)
    (show 1/(50*(1-η)^2)∈Icc 0 ((2:ℝ)⁻¹) from ⟨by positivity,by linarith⟩) hp.le
  have hmargin := conductance_entropy_margin hη hηmax
  nlinarith

end BreakingResonance
