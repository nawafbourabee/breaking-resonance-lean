import BreakingResonance.VerletTrajectory
import Mathlib.Analysis.Convex.Strong
import Mathlib.Analysis.Convex.Deriv

noncomputable section

open Set Filter Topology

namespace BreakingResonance

/-- The fast scalar potential in Section 7. -/
def fastPotential (curvNeg curvPos x : ℝ) : ℝ :=
  if 0 ≤ x then curvPos*x^2/2 else curvNeg*x^2/2

def fastGradient (curvNeg curvPos x : ℝ) : ℝ :=
  if 0 ≤ x then curvPos*x else curvNeg*x

theorem fastGradient_eq_max (curvNeg curvPos x : ℝ) :
    fastGradient curvNeg curvPos x = curvNeg*x+(curvPos-curvNeg)*max x 0 := by
  by_cases hx : 0 ≤ x
  · rw [fastGradient,ite_eq_left hx,max_eq_left hx]
    ring
  · rw [fastGradient,ite_eq_right hx,max_eq_right (le_of_not_ge hx),mul_zero,add_zero]

theorem fastGradient_continuous (curvNeg curvPos : ℝ) : Continuous (fastGradient curvNeg curvPos) := by
  have he : fastGradient curvNeg curvPos = fun x => curvNeg*x+(curvPos-curvNeg)*max x 0 :=
    funext (fastGradient_eq_max curvNeg curvPos)
  rw [he]
  fun_prop

private theorem scalar_quadratic_hasDerivAt (c x : ℝ) :
    HasDerivAt (fun y : ℝ => c*y^2/2) (c*x) x := by
  have hd : HasDerivAt (fun y : ℝ => y^2) (2*x) x := by
    simpa using hasDerivAt_pow 2 x
  have hc := (hd.const_mul c).div_const 2
  rw [show c*(2*x)/2 = c*x by ring] at hc
  exact hc

theorem fastPotential_hasDerivAt (curvNeg curvPos x : ℝ) :
    HasDerivAt (fastPotential curvNeg curvPos) (fastGradient curvNeg curvPos x) x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rw [fastGradient,ite_eq_right (not_le.mpr hx)]
    have hd := scalar_quadratic_hasDerivAt curvNeg x
    apply hd.congr_of_eventuallyEq
    filter_upwards [gt_mem_nhds hx] with y hy
    exact ite_eq_right (not_le.mpr hy)
  · have h0 : fastGradient curvNeg curvPos 0 = 0 := by simp [fastGradient]
    rw [h0,hasDerivAt_iff_tendsto_slope]
    have he : slope (fastPotential curvNeg curvPos) 0 = fun y => (1/2)*fastGradient curvNeg curvPos y := by
      funext y
      by_cases hy : y = 0
      · simp [hy,h0]
      · rw [slope_fun_def_field]
        simp only [fastPotential, fastGradient, le_refl, ite_true, zero_pow (by norm_num : 2 ≠ 0),
          mul_zero, zero_div, sub_zero]
        split_ifs <;> field_simp [hy] <;> ring
    rw [he]
    have hc := (show Continuous (fun y : ℝ => (1/2)*fastGradient curvNeg curvPos y) from
      continuous_const.mul (fastGradient_continuous curvNeg curvPos)).continuousAt (x := (0:ℝ))
    simpa only [ContinuousAt, h0, mul_zero] using hc.tendsto.mono_left nhdsWithin_le_nhds
  · rw [fastGradient,ite_eq_left hx.le]
    have hd := scalar_quadratic_hasDerivAt curvPos x
    apply hd.congr_of_eventuallyEq
    filter_upwards [lt_mem_nhds hx] with y hy
    exact ite_eq_left hy.le

/-- Every secant of the force is between the two scalar curvatures. -/
theorem fastGradient_secant {curvNeg curvPos x y : ℝ} (hcurv : curvNeg ≤ curvPos) (hxy : x ≤ y) :
    curvNeg*(y-x) ≤ fastGradient curvNeg curvPos y-fastGradient curvNeg curvPos x ∧
    fastGradient curvNeg curvPos y-fastGradient curvNeg curvPos x ≤ curvPos*(y-x) := by
  by_cases hx : 0 ≤ x
  · have hy := hx.trans hxy
    simp only [fastGradient,ite_eq_left hx,ite_eq_left hy]
    constructor <;> nlinarith only [mul_nonneg (sub_nonneg.mpr hcurv) (sub_nonneg.mpr hxy)]
  · by_cases hy : 0 ≤ y
    · simp only [fastGradient,ite_eq_right hx,ite_eq_left hy]
      constructor
      · nlinarith only [mul_nonneg (sub_nonneg.mpr hcurv) hy]
      · nlinarith only [mul_nonneg (sub_nonneg.mpr hcurv) (neg_nonneg.mpr (le_of_not_ge hx))]
    · simp only [fastGradient,ite_eq_right hx,ite_eq_right hy]
      constructor <;> nlinarith only [mul_nonneg (sub_nonneg.mpr hcurv) (sub_nonneg.mpr hxy)]

theorem fastGradient_lipschitz {curvNeg : ℝ} {curvPos : NNReal} (hcurv₀ : 0 ≤ curvNeg)
    (hcurv : curvNeg ≤ (curvPos:ℝ)) :
    LipschitzWith curvPos (fastGradient curvNeg curvPos) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  have hmono {x y : ℝ} (hxy : x ≤ y) :
      dist (fastGradient curvNeg curvPos x) (fastGradient curvNeg curvPos y) ≤ (curvPos:ℝ)*dist x y := by
    rw [dist_comm x y,dist_comm (fastGradient curvNeg curvPos x),Real.dist_eq,Real.dist_eq,
      abs_of_nonneg (sub_nonneg.mpr hxy), abs_of_nonneg
        ((mul_nonneg hcurv₀ (sub_nonneg.mpr hxy)).trans (fastGradient_secant hcurv hxy).1)]
    exact (fastGradient_secant hcurv hxy).2
  rcases le_total x y with hxy | hyx
  · exact hmono hxy
  · simpa only [dist_comm] using hmono hyx

theorem fastPotential_strongConvex {curvNeg curvPos : ℝ} (hcurv : curvNeg ≤ curvPos) :
    StrongConvexOn (univ : Set ℝ) curvNeg (fastPotential curvNeg curvPos) := by
  rw [strongConvexOn_iff_convex]
  let f (x : ℝ) := fastPotential curvNeg curvPos x-curvNeg/2*x^2
  let g (x : ℝ) := fastGradient curvNeg curvPos x-curvNeg*x
  have hd (x : ℝ) : HasDerivAt f (g x) x := by
    have hq : HasDerivAt (fun y => curvNeg/2*y^2) (curvNeg*x) x := by
      have he : (fun y : ℝ => curvNeg/2*y^2) = fun y => curvNeg*y^2/2 := by
        funext y; ring
      rw [he]
      exact scalar_quadratic_hasDerivAt curvNeg x
    exact (fastPotential_hasDerivAt curvNeg curvPos x).fun_sub hq
  have hm : Monotone g := by
    intro x y hxy
    dsimp [g]
    linarith only [(fastGradient_secant hcurv hxy).1]
  have hc := Monotone.convexOn_univ_of_deriv (fun x => (hd x).differentiableAt) (show Monotone (deriv f) by
    have he : deriv f = g := funext fun x => (hd x).deriv
    rwa [he])
  simpa only [f,Real.norm_eq_abs,sq_abs] using hc

end BreakingResonance

#print axioms BreakingResonance.fastPotential_hasDerivAt
#print axioms BreakingResonance.fastGradient_lipschitz
#print axioms BreakingResonance.fastPotential_strongConvex
