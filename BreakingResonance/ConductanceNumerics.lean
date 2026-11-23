import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-! Rational certificates for the numerical margin in the reference-conductance proof. -/
namespace BreakingResonance
open Set

theorem log_two_bounds : (6931:ℝ)/10000<Real.log 2 ∧ Real.log 2<(693148:ℝ)/1000000 := by
  have hl := Real.sum_range_le_log_div (by norm_num : (0:ℝ)≤1/3) (by norm_num : (1:ℝ)/3<1) 7
  have hu := Real.log_div_le_sum_range_add (by norm_num : (0:ℝ)≤1/3) (by norm_num : (1:ℝ)/3<1) 7
  norm_num [Finset.sum_range_succ] at hl hu
  constructor <;> linarith

theorem log_fifty_upper : Real.log 50<(3913:ℝ)/1000 := by
  have hl := Real.sum_range_le_log_div (by norm_num : (0:ℝ)≤7/57) (by norm_num : (7:ℝ)/57<1) 2
  norm_num [Finset.sum_range_succ] at hl
  have he : Real.log (50:ℝ)=6*Real.log 2-Real.log ((32:ℝ)/25) := by
    have hx : (50:ℝ)=2^6/((32:ℝ)/25) := by norm_num
    rw [hx,Real.log_div (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he]
  linarith [log_two_bounds.2]

theorem log_small_ratio_upper : Real.log ((358801:ℝ)/351601)<(20271:ℝ)/1000000 := by
  have hu := Real.log_div_le_sum_range_add (by norm_num : (0:ℝ)≤3600/355201)
    (by norm_num : (3600:ℝ)/355201<1) 2
  norm_num [Finset.sum_range_succ] at hu
  linarith

theorem binary_entropy_at_cutoff : Real.binEntropy ((7200:ℝ)/358801)+
    (41:ℝ)/(48*599)+(49:ℝ)/(72*600)<(101:ℝ)/1000 := by
  have hl : Real.log (((7200:ℝ)/358801)⁻¹)<(3913:ℝ)/1000 := by
    apply lt_of_le_of_lt (Real.log_le_log (by norm_num) (by norm_num)) log_fifty_upper
  have hu := log_small_ratio_upper
  rw [Real.binEntropy]
  norm_num at hl hu ⊢
  linarith

theorem conductance_entropy_margin {η : ℝ} (hη : 0<η) (hηmax : η≤1/600) :
    Real.binEntropy (1/(50*(1-η)^2))+
      41*η/(48*(1-η))+49*η/72<(7:ℝ)/48*Real.log 2 := by
  have hd : 0<1-η := by linarith
  have hdmin : (599:ℝ)/600≤1-η := by linarith
  have hp : 1/(50*(1-η)^2)≤(7200:ℝ)/358801 := by
    have hs := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤599/600) hdmin 2
    have hh := one_div_le_one_div_of_le (by norm_num : (0:ℝ)<50*((599:ℝ)/600)^2)
      (mul_le_mul_of_nonneg_left hs (by norm_num : (0:ℝ)≤50))
    norm_num at hh
    simpa [div_eq_mul_inv,mul_comm] using hh
  have hp0 : 0≤1/(50*(1-η)^2) := by positivity
  have hmono := Real.binEntropy_strictMonoOn.monotoneOn
    (show 1/(50*(1-η)^2)∈Icc 0 ((2:ℝ)⁻¹) from ⟨hp0,by linarith⟩)
    (show (7200:ℝ)/358801∈Icc 0 ((2:ℝ)⁻¹) by norm_num) hp
  have he1 : 41*η/(48*(1-η))≤(41:ℝ)/(48*599) := by
    apply (div_le_iff₀ (by positivity : 0<48*(1-η))).mpr
    nlinarith
  have he2 : 49*η/72≤(49:ℝ)/(72*600) := by linarith
  linarith [binary_entropy_at_cutoff,log_two_bounds.1]

end BreakingResonance
