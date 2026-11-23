import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic

/-! Weighted integration of a continuous upper bound for the derivative's increments. -/
namespace BreakingResonance
noncomputable section
open MeasureTheory Set
open scoped Topology

theorem integral_primitive_eq_weighted (Q : ℝ → ℝ) (hQ : Continuous Q) (a b : ℝ) :
    (∫t in a..b, ∫r in a..t, Q r) = ∫t in a..b, (b-t)*Q t := by
  let F : ℝ → ℝ := fun t=>∫r in a..t,Q r
  have hFd (t : ℝ) : HasDerivAt F (Q t) t :=
    intervalIntegral.integral_hasDerivAt_right (hQ.intervalIntegrable a t)
      hQ.stronglyMeasurable.stronglyMeasurableAtFilter hQ.continuousAt
  have hF : Continuous F := continuous_iff_continuousAt.mpr (fun t=>(hFd t).continuousAt)
  have hh := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u:=fun t=>b-t) (v:=F) (u':=fun _=>(-1:ℝ)) (v':=Q)
    (a:=a) (b:=b)
    (fun t _=>by simpa using (hasDerivAt_id t).const_sub b)
    (fun t _=>hFd t) intervalIntegrable_const (hQ.intervalIntegrable a b)
  simp only [sub_self,zero_mul,F,intervalIntegral.integral_same,mul_zero,zero_sub,
    neg_one_mul,intervalIntegral.integral_neg,neg_neg] at hh
  exact hh.symm

theorem weighted_increment_bound {W C Q : ℝ → ℝ} {a b : ℝ}
    (hab : a≤b) (hC : Continuous C) (hQ : Continuous Q)
    (hW : ∀ t∈Icc a b,HasDerivAt W (C t) t)
    (hinc : ∀ t∈Icc a b,C t-C a≤∫r in a..t,Q r) :
    W b-W a≤(b-a)*C a+(∫t in a..b,(b-t)*Q t) := by
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht=>hW t (by simpa only [uIcc_of_le hab] using ht))
    (hC.intervalIntegrable a b)
  let F : ℝ → ℝ := fun t=>∫r in a..t,Q r
  have hFd (t : ℝ) : HasDerivAt F (Q t) t :=
    intervalIntegral.integral_hasDerivAt_right (hQ.intervalIntegrable a t)
      hQ.stronglyMeasurable.stronglyMeasurableAtFilter hQ.continuousAt
  have hF : Continuous F := continuous_iff_continuousAt.mpr (fun t=>(hFd t).continuousAt)
  have hh := intervalIntegral.integral_mono_on (μ:=volume) hab
    (hC.intervalIntegrable a b) ((continuous_const.add hF).intervalIntegrable a b)
    (fun t ht=>show C t≤C a+F t by have hi:=hinc t ht; dsimp [F]; linarith)
  simp only [Pi.add_apply] at hh
  rw [intervalIntegral.integral_add (intervalIntegrable_const (c:=C a)) (hF.intervalIntegrable a b),
    intervalIntegral.integral_const] at hh
  simp only [smul_eq_mul,F] at hh
  rw [integral_primitive_eq_weighted Q hQ a b,hFTC] at hh
  exact hh

end
end BreakingResonance
