import BreakingResonance.ProposalEntropy
import BreakingResonance.RestrictedRejection

noncomputable section

open MeasureTheory ProbabilityTheory Set PersistencePays
open scoped ENNReal Gradient

namespace BreakingResonance

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- A uniform physical time bound gives a uniform acceptance bound on the energy shell. -/
theorem shell_acceptance {U : E → ℝ} {m L LH : ℝ}
    (a : A1 U m L) (hmin : U a.minimizer = 0)
    (hLH : 0 ≤ LH) (henergy : PPModifiedEnergy U LH)
    {h Tstar R η : ℝ} (hh : 0 < h) (_hT : 0 ≤ Tstar) (hR : 1 ≤ R) (hη : 0 ≤ η)
    (hη₁ : η ≤ 1) (hbudget : h^2*(L*R+LH*Tstar*R*Real.sqrt R) ≤ η/3)
    (j : ℕ) (hj : (j:ℝ)*h ≤ Tstar) (z : E×E) (hz : phaseEnergy U z ≤ R) :
    ENNReal.ofReal (1-η) ≤ acceptProbability
      (fun z => phaseEnergy U z-phaseEnergy U (trajectory (gradient U) h z j)) z := by
  let aT := LH*((j:ℝ)*h)*h^2*R*Real.sqrt R
  let b := h^2*L*R
  have hL := a.L_pos
  have hR₀ : 0 ≤ R := by linarith
  have hU (x : E) : 0 ≤ U x := hmin ▸ a.minimizer_le x
  have hA : 0 ≤ aT := by dsimp [aT]; positivity
  have hB : 0 ≤ b := by dsimp [b]; positivity
  have hcap : aT+b ≤ η/3 := by
    have ht := mul_le_mul_of_nonneg_left hj
      (show 0 ≤ LH*h^2*R*Real.sqrt R by positivity)
    dsimp [aT,b]
    nlinarith only [ht,hbudget]
  have hhsq : h^2*L ≤ 1 := by
    have hb : b ≤ η/3 := by linarith only [hcap,hA]
    have ht := mul_le_mul_of_nonneg_left hR (show 0 ≤ h^2*L by positivity)
    change h^2*L*1 ≤ b at ht
    linarith only [ht,hb,hη₁]
  have hb : 2*aT+b/2 ≤ R := by linarith only [hcap,hB,hη₁,hR]
  have hrem (w : E×E) :
      |modifiedEnergy U (gradient U) h (verlet (gradient U) h w) -
          modifiedEnergy U (gradient U) h w| ≤
        LH/12*h^3*‖flightVelocity (gradient U) h w‖^3 := by
    obtain ⟨he,hr⟩ := henergy h hh w
    rw [he]
    convert hr using 1
    ring
  have hE := (verlet_energy_control_with_modified_error_of_remainder U
    (gradient U) (hessian U) a.hasGradientAt a.hasHessianAt a.continuous_hessian
    L LH h R a.L_pos hLH hh.le hR₀ hU a.upper hrem hhsq j hb z hz j le_rfl).2.2.1
  change |phaseEnergy U (trajectory (gradient U) h z j)-phaseEnergy U z| ≤ 2*aT+b at hE
  have herror : phaseEnergy U (trajectory (gradient U) h z j)-phaseEnergy U z ≤ η := by
    have h := (abs_le.mp hE).2
    linarith only [h,hcap,hB,hη]
  exact ENNReal.ofReal_le_ofReal (metropolisAcceptance_lower U (gradient U) h z j η hη herror)

end BreakingResonance

#print axioms BreakingResonance.shell_acceptance
