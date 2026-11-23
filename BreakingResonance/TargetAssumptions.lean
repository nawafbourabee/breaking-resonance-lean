import BreakingResonance.Reversibility
import PersistencePays.GibbsRegularity
import Mathlib.Analysis.Convex.Strong
import Mathlib.Analysis.Convex.Deriv

noncomputable section

open MeasureTheory ProbabilityTheory Set PersistencePays
open scoped Gradient InnerProductSpace RealInnerProductSpace ENNReal

namespace BreakingResonance

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The paper's strong convexity, gradient Lipschitz continuity, and C²
regularity imply the Hessian bounds used in the transport development. -/
theorem target_hessian_bounds (U : E → ℝ) {m : ℝ} {L : NNReal}
    (hd : 0 < Module.finrank ℝ E) (hm : 0 < m)
    (hsc : StrongConvexOn (univ : Set E) m U)
    (hLip : LipschitzWith L (gradient U)) (hU : ContDiff ℝ 2 U) :
    A1 U m (L:ℝ) := by
  have hgrad (x : E) : HasGradientAt U (gradient U x) x :=
    ((hU.differentiable (by norm_num)) x).hasGradientAt
  have hHess (x : E) : HasFDerivAt (gradient U) (hessian U x) x :=
    ((contDiff_gradient_of_twice_contDiff U hU).differentiable (by norm_num) x).hasFDerivAt
  have hlu (x u : E) : m*‖u‖^2 ≤ ⟪hessian U x u,u⟫_ℝ := by
    let C (y : E) := U y-m/2*‖y‖^2
    let F (t : ℝ) := C (x+t • u)
    let J (t : ℝ) := ⟪gradient U (x+t • u),u⟫_ℝ - m*⟪x+t • u,u⟫_ℝ
    have hC : ConvexOn ℝ (univ : Set E) C := strongConvexOn_iff_convex.mp hsc
    have hF : ConvexOn ℝ (univ : Set ℝ) F := by
      have he (t : ℝ) : AffineMap.lineMap x (x+u) t = x+t • u := by
        simp [AffineMap.lineMap_apply,add_comm]
      have h := hC.comp_affineMap (AffineMap.lineMap x (x+u))
      change ConvexOn ℝ (univ : Set ℝ) (fun t => C (AffineMap.lineMap x (x+u) t)) at h
      have he' : (fun t => C (AffineMap.lineMap x (x+u) t)) = F :=
        funext fun t => congrArg C (he t)
      rwa [he'] at h
    have hline (t : ℝ) : HasDerivAt (fun s : ℝ => x+s • u) u t := by
      simpa using ((hasDerivAt_id t).smul_const u).const_add x
    have hder (t : ℝ) : HasDerivAt F (J t) t := by
      have h := (potential_line_derivative U (gradient U) hgrad x u t).fun_sub
        ((hline t).norm_sq.const_mul (m/2))
      have he : ⟪gradient U (x+t • u),u⟫_ℝ-(m/2)*(2*⟪x+t • u,u⟫_ℝ) = J t := by
        dsimp [J]
        ring
      rw [← he]
      exact h
    have hmon : Monotone J := by
      intro t s hts
      have h := hF.monotoneOn_deriv (fun t _ => (hder t).differentiableAt)
        (mem_univ t) (mem_univ s) hts
      rwa [(hder t).deriv,(hder s).deriv] at h
    have hj : HasDerivAt J (⟪hessian U x u,u⟫_ℝ - m*‖u‖^2) 0 := by
      have h := (gradient_line_derivative (gradient U) (hessian U) hHess x u 0).fun_sub
        (((hline 0).inner ℝ (hasDerivAt_const 0 u)).const_mul m)
      simpa [J,real_inner_self_eq_norm_sq] using h
    have hz := hmon.deriv_nonneg (x := 0)
    rw [hj.deriv] at hz
    exact sub_nonneg.mp hz
  have huu (x u : E) : ⟪hessian U x u,u⟫_ℝ ≤ (L:ℝ)*‖u‖^2 := by
    have hn : ‖hessian U x‖ ≤ (L:ℝ) := norm_fderiv_le_of_lipschitz ℝ hLip
    have ha := (ContinuousLinearMap.le_opNorm (hessian U x) u).trans
      (mul_le_mul_of_nonneg_right hn (norm_nonneg u))
    have h := real_inner_le_norm (hessian U x u) u
    nlinarith only [h,mul_le_mul_of_nonneg_right ha (norm_nonneg u)]
  have hmL : m ≤ (L:ℝ) := by
    obtain ⟨u,hu⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hd
    have h := (hlu 0 u).trans (huu 0 u)
    exact le_of_mul_le_mul_right h (sq_pos_of_pos (norm_pos_iff.mpr hu))
  exact ⟨hU,hm,hmL,hlu,huu⟩

theorem gradient_sub_const_eq (U : E → ℝ) (c : ℝ) :
    gradient (fun x => U x-c) = gradient U := by
  funext x
  unfold gradient
  rw [fderiv_sub_const]

theorem shifted_target_hessian_bounds {U : E → ℝ} {m L : ℝ}
    (a : A1 U m L) (c : ℝ) : A1 (fun x => U x-c) m L := by
  have h : hessian (fun x => U x-c) = hessian U := by
    unfold hessian
    rw [gradient_sub_const_eq]
  exact ⟨a.twice_contDiff.sub contDiff_const,a.m_pos,a.m_le_L,
    h.symm ▸ a.lower,h.symm ▸ a.upper⟩

theorem shifted_target_minimum_zero {U : E → ℝ} {m L : ℝ} (a : A1 U m L) :
    let V (x : E) := U x-U a.minimizer
    let av := shifted_target_hessian_bounds a (U a.minimizer)
    V av.minimizer = 0 := by
  let V (x : E) := U x-U a.minimizer
  let av := shifted_target_hessian_bounds a (U a.minimizer)
  have he : av.minimizer = a.minimizer :=
    (av.minimizer_unique a.minimizer (fun y => sub_le_sub_right (a.minimizer_le y) _)).symm
  change V av.minimizer = 0
  rw [he]
  exact sub_self _

theorem positionGibbs_sub_const (U : E → ℝ) (c : ℝ) :
    positionGibbs (fun x => U x-c) = positionGibbs U := by
  ext A hA
  unfold positionGibbs
  rw [tilted_apply' _ _ hA, tilted_apply' _ _ hA]
  have he (x : E) : Real.exp ((-(fun y => U y-c)) x) = Real.exp c*Real.exp (-U x) := by
    change Real.exp (-(U x-c)) = _
    rw [show -(U x-c) = c+(-U x) by ring,Real.exp_add]
  simp_rw [he]
  rw [integral_const_mul]
  simp_rw [mul_div_mul_left _ _ (Real.exp_ne_zero c)]
  rfl

theorem roundedVerletKernel_sub_const (U : E → ℝ) (hU : Measurable U)
    (g : E → E) (hg : Measurable g) (c h : ℝ) (ρ : Measure ℝ) [IsProbabilityMeasure ρ] :
    roundedVerletKernel (fun x => U x-c) (hU.sub measurable_const) g hg h ρ =
      roundedVerletKernel U hU g hg h ρ := by
  have he : verletLogAcceptance (fun x => U x-c) g h = verletLogAcceptance U g h := by
    funext z
    simp only [verletLogAcceptance,phaseEnergy_eq_norm]
    ring
  unfold roundedVerletKernel randomizedVerletKernel
  congr

end BreakingResonance

#print axioms BreakingResonance.target_hessian_bounds
#print axioms BreakingResonance.positionGibbs_sub_const
#print axioms BreakingResonance.roundedVerletKernel_sub_const
