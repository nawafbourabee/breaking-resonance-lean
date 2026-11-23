import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! A two-sided coupling estimate identifies the derivative of the transport cost. -/
namespace BreakingResonance
open Filter Set
open scoped Topology

theorem hasDerivAt_of_quadratic_upper_bounds {W C : ℝ → ℝ} {M : ℝ}
    (hM : 0≤M) (hC : Continuous C)
    (hupper : ∀ x y, W y≤W x+(y-x)*C x+(M/2)*(y-x)^2) (x : ℝ) :
    HasDerivAt W (C x) x := by
  have herr (y : ℝ) : |W y-W x-(y-x)*C x|≤
      |y-x| *|C y-C x|+(M/2)*(y-x)^2 := by
    apply abs_le.mpr
    have hu := hupper x y
    have hl := hupper y x
    have hab : -(|y-x| *|C y-C x|)≤(y-x)*(C y-C x) := by
      simpa only [abs_mul] using neg_abs_le ((y-x)*(C y-C x))
    constructor
    · nlinarith
    · nlinarith [mul_nonneg (abs_nonneg (y-x)) (abs_nonneg (C y-C x))]
  have hb (y : ℝ) : ‖y-x‖⁻¹*‖W y-W x-(y-x) • C x‖ ≤
      |C y-C x|+(M/2)*|y-x| := by
    simp only [Real.norm_eq_abs,smul_eq_mul]
    by_cases h : y=x
    · simp [h]
    · apply (inv_mul_le_iff₀ (abs_pos.mpr (sub_ne_zero.mpr h))).mpr
      have he := sq_abs (y-x)
      nlinarith [herr y]
  have ht : Tendsto (fun y : ℝ=>|C y-C x|+(M/2)*|y-x|) (𝓝 x) (𝓝 0) := by
    have hh := (((hC.continuousAt : ContinuousAt C x).sub_const (C x)).abs).add
      ((((continuousAt_id : ContinuousAt (fun y : ℝ=>y) x).sub_const x).abs).const_mul (M/2))
    simpa only [id_eq,sub_self,abs_zero,mul_zero,add_zero,zero_add] using hh
  apply hasDerivAt_iff_tendsto.mpr
  exact squeeze_zero (fun y=>mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _)) hb ht

end BreakingResonance
