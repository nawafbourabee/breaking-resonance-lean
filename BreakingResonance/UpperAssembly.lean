import BreakingResonance.RestrictedMixing
import BreakingResonance.RestrictedVerlet
import BreakingResonance.LowerSpectralBound
import BreakingResonance.UpperConstants
import BreakingResonance.TargetAssumptions

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory Set PersistencePays
open scoped ENNReal Gradient

namespace BreakingResonance

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Theorem 1 with the explicit law-dependent retained mass used in (3.4).
This statement uses the normalization of the potential in Section 6. -/
theorem theoremOne_explicit_normalized (hPP : PPInterpolation E)
    {U : E → ℝ} {m L LH : ℝ} (a : A1 U m L) (hLH : 0 ≤ LH)
    (hlip : A2 U LH) (hTI : TalagrandBound a) (hmin : U a.minimizer = 0)
    (ρ : Measure ℝ) [IsProbabilityMeasure ρ] {bρ δρ : ℝ}
    (hρ : NonresonantDuration ρ m bρ δρ)
    (ν : Measure E) [IsProbabilityMeasure ν] (hac : ν ≪ positionGibbs U)
    {M ε : ℝ} (hM : 1 ≤ M) (hε : 0 < ε) (hε₁ : ε ≤ 1)
    (hL2 : MemLp (fun x => (ν.rnDeriv (positionGibbs U) x).toReal) 2 (positionGibbs U))
    (hwarm : ‖hL2.toLp (fun x => (ν.rnDeriv (positionGibbs U) x).toReal)‖ ≤ M)
    (N n : ℕ)
    (hN : let D := 1+(Module.finrank ℝ E:ℝ)+Real.log (M/ε)
      upperC₁ bρ δρ*(Real.sqrt (L/m*D)+Real.sqrt LH*(D/m)^(3/4:ℝ)) ≤ (N:ℝ))
    (hn : let pS := ρ.real (Iic (upperDurationCutoff m bρ δρ))
      let φP := pS*upperFourierConstant bρ δρ/60
      6/(upperSpectralConstant bρ δρ*φP^2)*Real.log (2*M/ε) ≤ (n:ℝ)) :
    let h := 4/((N:ℝ)*Real.sqrt m)
    let P := roundedVerletKernel U a.twice_contDiff.continuous.measurable (gradient U)
      (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable h ρ
    totalVariation (evolve (fun _ => P) ν n) (positionGibbs U) ≤ ENNReal.ofReal ε := by
  let d := Module.finrank ℝ E
  let D := 1+(d:ℝ)+Real.log (M/ε)
  let τstar := upperDurationCutoff m bρ δρ
  let c := upperFourierConstant bρ δρ
  let βP := upperSpectralConstant bρ δρ
  let η := c/600
  let CT := upperHorizonFactor bρ δρ
  let CR := 2*Real.log (64/η)
  let pS := ρ.real (Iic τstar)
  let φP := pS*c/60
  let s := ε^4/(64*M^4)
  let R := 3*(d:ℝ)*Real.log 2+2*Real.log (1/(η*s))
  let h := 4/((N:ℝ)*Real.sqrt m)
  let π := positionGibbs U
  let hU := a.twice_contDiff.continuous.measurable
  let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
  let P := roundedVerletKernel U hU (gradient U) hg h ρ
  let : IsProbabilityMeasure π := a.gibbs_isProbabilityMeasure
  let : IsProbabilityMeasure (phaseGibbs U) := by unfold phaseGibbs; infer_instance
  obtain ⟨hc,hβ⟩ := upperConstants_fourier_pos hρ.b_pos hρ.gap_pos hρ.gap_le_one
  have hη : 0 < η := div_pos hc.1 (by norm_num)
  have hη₁ : η ≤ 1/600 := div_le_div_of_nonneg_right hc.2 (by norm_num)
  have hbpos := hρ.b_pos
  have hδpos := hρ.gap_pos
  have hCT : 0 < CT := by dsimp [CT,upperHorizonFactor]; positivity
  have ⟨hτ,htcut⟩ := duration_cutoff_tail ρ hρ
  have htailCut : ρ.real (Ioi τstar) ≤ δρ/4 := htcut
  have hps₀ : 0 < pS := (by linarith only [hρ.gap_le_one] : 0 < 1-δρ/4).trans_le
    (retained_duration_lower ρ htailCut)
  have hps₁ : pS ≤ 1 := measureReal_le_one
  have hφ : 0 < φP := div_pos (mul_pos hps₀ hc.1) (by norm_num)
  have hφ₁ : φP ≤ 1 := by
    have h := mul_le_mul hps₁ hc.2 hc.1.le (by norm_num : (0:ℝ) ≤ 1)
    dsimp [φP]
    linarith only [h]
  obtain ⟨hs,hD,hR,hRD,hCR,hcut_eq⟩ := mixing_cutoff_parameters hM hε hε₁ hη hη₁ d
  have hR' : 1 ≤ R := hR
  have hs' : 0 < s := hs.1
  have hsmallS : s ≤ 1/2 := hs.2.trans (by norm_num)
  obtain ⟨hNp,hNδ,hhm,hbudget⟩ := mixing_step_parameters a.m_pos a.m_le_L
    hLH hρ.gap_pos hρ.gap_le_one hη hCT hCR hD (by linarith only [hR']) hRD N hN
  have ht := a.gibbs_energy_tail R
  rw [energy_tail_constant,show Module.finrank ℝ E = d from rfl,
    show (2:ℝ)^(3*(d:ℝ)/2)*Real.exp (-R/2) = η*s from hcut_eq] at ht
  have htail : (phaseGibbs U).real {z | R < phaseEnergy U z} ≤ η*s := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top ht
    rw [ENNReal.toReal_ofReal (mul_nonneg hη.le hs'.le)] at h
    simpa only [hmin,sub_zero,Measure.real] using h
  have hNp' : 0 < N := by omega
  have hf := roundedFourierBounds ρ hρ τstar hτ htailCut N hNp' h rfl hhm
  have hmatch : Real.sqrt m*τstar = 4*bρ/δρ := cutoff_rescaled a.m_pos hρ.gap_pos
  dsimp only at hf
  rw [hmatch] at hf
  have hcompare θ (hθ : θ ∈ Icc (-Real.pi) Real.pi) :=
    (hf.2.2 θ hθ).1
  have hgap θ (hθ : θ ∈ Icc (-Real.pi) Real.pi) :=
    (hf.2.2 θ hθ).2
  have hbudget' : h^2*(L*R+LH*(τstar+4/Real.sqrt m)*R*Real.sqrt R) ≤ η/3 := by
    rw [horizon_rescaled a.m_pos hρ.gap_pos]
    exact hbudget
  have hcond := propositionC hPP a hLH hlip hTI hmin ρ hρ hτ htailCut hc.1 hc.2
    hs' hsmallS hR' N hNp hNδ hcompare htail hbudget'
  have hspectral := roundedVerlet_lower_spectral_of_fourier U hU a.gibbs_integrable
    (gradient U) hg h ρ hβ.2 hgap
  obtain ⟨hrev,hspec⟩ := hspectral
  have htvm := propositionA π P hrev hs' hsmallS hφ hφ₁ hβ.1 hβ.2 hcond hspec
    ν hac hL2 hwarm hε hε₁ n
  have hM₀ : 0 < M := by linarith
  have hm := theoremOne_mass_substitution M ε hM₀ hε
  change totalVariation (evolve (fun _ => P) ν n) π ≤ ENNReal.ofReal ε
  change _ ≤ ENNReal.ofReal (ε/2+1/2*Real.sqrt
    (Real.exp (-(n:ℝ)*βP*φP^2/2)*(4*M^2/ε)+2*s*(4*M^2/ε)^2)) at htvm
  rw [show 2*s*(4*M^2/ε)^2 = ε^2/2 from hm] at htvm
  have hn' := mixing_iteration_threshold hM hε hβ.1 hφ hn
  exact htvm.trans (ENNReal.ofReal_le_ofReal
    (theoremOne_error_bound M ε βP φP n _ hM₀ hε hβ.1 hφ hn' le_rfl))

end BreakingResonance

#print axioms BreakingResonance.theoremOne_explicit_normalized
