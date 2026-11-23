import BreakingResonance.AdjustedComparison
import BreakingResonance.RoundedFourierBounds
import BreakingResonance.SpectralDecay

noncomputable section

open MeasureTheory ProbabilityTheory Set PersistencePays
open scoped RealInnerProductSpace ENNReal Gradient

namespace BreakingResonance

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The full count law's Fourier bound gives the claimed inequality for the actual position kernel. -/
theorem roundedVerlet_lower_spectral_of_fourier
    (U : E → ℝ) (hU : Measurable U) (hZ : Integrable (fun x => Real.exp (-U x)) volume)
    (g : E → E) (hg : Measurable g) (h : ℝ) (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    {βP : ℝ} (hβP : βP ≤ 1)
    (hgap : ∀ θ ∈ Icc (-Real.pi) Real.pi,
      βP ≤ 1+cosineSeries (countLawWeight (roundedDurationLaw h ρ)) θ) :
    let π := positionGibbs U
    let P := roundedVerletKernel U hU g hg h ρ
    letI : IsProbabilityMeasure π := isProbabilityMeasure_tilted hZ
    ∃ hrev : Kernel.IsReversible P π, ∀ f : Lp ℝ 2 π,
      βP*markovDirichlet π P f ≤ ‖f‖^2-‖markovL2 π P hrev.invariant f‖^2 := by
  dsimp only
  let π := positionGibbs U
  let P := roundedVerletKernel U hU g hg h ρ
  letI : IsProbabilityMeasure π := isProbabilityMeasure_tilted hZ
  have hrev : Kernel.IsReversible P π := roundedVerletKernel_reversible U hU hZ g hg h ρ
  refine ⟨hrev, fun f => ?_⟩
  change βP*markovDirichlet π P f ≤ ‖f‖^2-‖markovL2 π P hrev.invariant f‖^2
  rw [markovDirichlet_eq_norm_sub π P hrev.invariant]
  apply spectralGap_decay (markovL2 π P hrev.invariant)
    (markovL2_symmetric π P hrev.invariant hrev)
    (markovL2_norm_le π P hrev.invariant) hβP
  intro f
  rw [realLp_norm_sq, markovL2_inner_quadratic π P hrev.invariant]
  exact randomizedVerletKernel_lower_l2 U hU hZ g hg h (roundedDurationLaw h ρ) βP
    (fun θ hθ => by linarith only [hgap θ hθ]) f

/-- Proposition B. The differentiability and Lipschitz-gradient parts of (A2)
suffice for the regularity of this kernel. The finite normalizer is as in (2.1). -/
theorem propositionB (U : E → ℝ) (hU : Differentiable ℝ U) {L : NNReal}
    (hL : LipschitzWith L (gradient U))
    (hZ : Integrable (fun x => Real.exp (-U x)) volume)
    (ρ : Measure ℝ) [IsProbabilityMeasure ρ] {m bρ δρ : ℝ}
    (hρ : NonresonantDuration ρ m bρ δρ) (N : ℕ) (hN : 1 ≤ N)
    (hhm : (4/((N:ℝ)*Real.sqrt m))^2*m ≤ δρ/16) :
    let h := 4/((N:ℝ)*Real.sqrt m)
    let kρ := evenHarmonic (2*(bρ+1))
    let ζρ := δρ/(2*(kρ:ℝ)^2)
    let βP := 1-Real.cos (ζρ/2)
    let π := positionGibbs U
    let P := roundedVerletKernel U hU.continuous.measurable (gradient U)
      hL.continuous.measurable h ρ
    letI : IsProbabilityMeasure π := isProbabilityMeasure_tilted hZ
    (0 < βP ∧ βP ≤ 1) ∧
      ∃ hrev : Kernel.IsReversible P π, ∀ f : Lp ℝ 2 π,
        βP*markovDirichlet π P f ≤ ‖f‖^2-‖markovL2 π P hrev.invariant f‖^2 := by
  dsimp only
  let h : ℝ := 4/((N:ℝ)*Real.sqrt m)
  let kρ := evenHarmonic (2*(bρ+1))
  let ζρ := δρ/(2*(kρ:ℝ)^2)
  have hh : 0 < h := by
    have hN' : 0 < (N:ℝ) := by exact_mod_cast (show 0 < N by omega)
    exact div_pos (by norm_num) (mul_pos hN' (Real.sqrt_pos_of_pos hρ.m_pos))
  have hx : 0 < 2*(bρ+1) := by linarith only [hρ.b_pos]
  have hz : 0 < ζρ ∧ ζρ ≤ 1 :=
    evenHarmonic_divisor_bounds hx hρ.gap_pos hρ.gap_le_one (by norm_num)
  have hβ := bernoulli_gap_bounds hz.1 hz.2
  refine ⟨⟨hβ.1,hβ.2.trans hz.2⟩, ?_⟩
  apply roundedVerlet_lower_spectral_of_fourier U hU.continuous.measurable hZ
    (gradient U) hL.continuous.measurable h ρ (hβ.2.trans hz.2)
  intro θ hθ
  exact roundedDuration_full_gap ρ hρ h hh hhm θ (abs_le.mpr hθ)

end BreakingResonance

#print axioms BreakingResonance.roundedVerlet_lower_spectral_of_fourier
#print axioms BreakingResonance.propositionB
