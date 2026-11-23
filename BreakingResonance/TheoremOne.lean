import BreakingResonance.UpperAssembly

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory Set PersistencePays
open scoped Gradient ENNReal

namespace BreakingResonance

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Lemma 6.3, stated for finite relative entropy. The extended-valued
transport cost records finiteness as well as the numerical bound. -/
def PaperTalagrand (m : ℝ) (π : Measure E) [IsProbabilityMeasure π] : Prop :=
  ∀ μ : ProbabilityMeasure E, klDiv (μ : Measure E) π ≠ ∞ →
    QuadraticTransport.cost μ (⟨π,inferInstance⟩ : ProbabilityMeasure E) ≤
      ENNReal.ofReal (2*(klDiv (μ : Measure E) π).toReal/m)

theorem roundedVerletKernel_congr_gradient
    (U : E → ℝ) (hU : Measurable U) {g g' : E → E}
    (hg : Measurable g) (hg' : Measurable g') (h : ℝ) (ρ : Measure ℝ)
    [IsProbabilityMeasure ρ] (he : g = g') :
    roundedVerletKernel U hU g hg h ρ = roundedVerletKernel U hU g' hg' h ρ := by
  subst g'
  rfl

theorem upperC₂_law_bound (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    {m bρ δρ : ℝ} (hρ : NonresonantDuration ρ m bρ δρ) :
    let pS := ρ.real (Iic (upperDurationCutoff m bρ δρ))
    let φP := pS*upperFourierConstant bρ δρ/60
    6/(upperSpectralConstant bρ δρ*φP^2) ≤ upperC₂ bρ δρ := by
  let pS := ρ.real (Iic (upperDurationCutoff m bρ δρ))
  let c := upperFourierConstant bρ δρ
  let β := upperSpectralConstant bρ δρ
  let φ := pS*c/60
  let φ₀ := (1-δρ/4)*c/60
  obtain ⟨hc,hβ⟩ := upperConstants_fourier_pos hρ.b_pos hρ.gap_pos hρ.gap_le_one
  have hp : 0 < 1-δρ/4 := by linarith only [hρ.gap_le_one]
  have hf₀ : 0 < φ₀ := div_pos (mul_pos hp hc.1) (by norm_num)
  have hret := retained_duration_lower ρ (duration_cutoff_tail ρ hρ).2
  have hφ : φ₀ ≤ φ :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hret hc.1.le) (by norm_num)
  change 6/(β*φ^2) ≤ 6/(β*φ₀^2)
  exact div_le_div_of_nonneg_left (by norm_num) (mul_pos hβ.1 (sq_pos_of_pos hf₀))
    (mul_le_mul_of_nonneg_left ((sq_le_sq₀ hf₀.le (hf₀.le.trans hφ)).mpr hφ) hβ.1.le)

/-- Theorem 1. The explicit constants are uniform over laws with fixed
non-resonance parameters. The two cited transport inequalities are
displayed as inputs. The conclusion uses the original potential. -/
theorem theoremOne (hPP : PPInterpolation E)
    (U : E → ℝ) {m : ℝ} {L : NNReal} {LH : ℝ}
    (hd : 0 < Module.finrank ℝ E) (hm : 0 < m)
    (hsc : StrongConvexOn (univ : Set E) m U) (hLip : LipschitzWith L (gradient U))
    (hU : ContDiff ℝ 2 U) (hLH : 0 ≤ LH)
    (hHess : ∀ x y, ‖hessian U x-hessian U y‖ ≤ LH*‖x-y‖)
    (hTal : let a := target_hessian_bounds U hd hm hsc hLip hU
      letI : IsProbabilityMeasure (positionGibbs U) := a.gibbs_isProbabilityMeasure
      PaperTalagrand m (positionGibbs U))
    (ρ : Measure ℝ) [IsProbabilityMeasure ρ] {bρ δρ : ℝ}
    (hρ : NonresonantDuration ρ m bρ δρ)
    (ν : Measure E) [IsProbabilityMeasure ν] (hac : ν ≪ positionGibbs U)
    {M ε : ℝ} (hM : 1 ≤ M) (hε : 0 < ε) (hε₁ : ε ≤ 1)
    (hL2 : MemLp (fun x => (ν.rnDeriv (positionGibbs U) x).toReal) 2 (positionGibbs U))
    (hwarm : ‖hL2.toLp (fun x => (ν.rnDeriv (positionGibbs U) x).toReal)‖ ≤ M)
    (N n : ℕ)
    (hN : let D := 1+(Module.finrank ℝ E:ℝ)+Real.log (M/ε)
      upperC₁ bρ δρ*(Real.sqrt ((L:ℝ)/m*D)+Real.sqrt LH*(D/m)^(3/4:ℝ)) ≤ (N:ℝ))
    (hn : upperC₂ bρ δρ*Real.log (2*M/ε) ≤ (n:ℝ)) :
    let h := 4/((N:ℝ)*Real.sqrt m)
    let P := roundedVerletKernel U hU.continuous.measurable (gradient U)
      hLip.continuous.measurable h ρ
    totalVariation (evolve (fun _ => P) ν n) (positionGibbs U) ≤ ENNReal.ofReal ε := by
  let a := target_hessian_bounds U hd hm hsc hLip hU
  let u₀ := U a.minimizer
  let V (x : E) := U x-u₀
  let av := shifted_target_hessian_bounds a u₀
  have hmin := shifted_target_minimum_zero a
  let π := positionGibbs U
  let πv := positionGibbs V
  let : IsProbabilityMeasure π := a.gibbs_isProbabilityMeasure
  let : IsProbabilityMeasure πv := av.gibbs_isProbabilityMeasure
  have hπ : πv = π := positionGibbs_sub_const U u₀
  have hgrad : gradient V = gradient U := gradient_sub_const_eq U u₀
  have hhess : hessian V = hessian U := by
    unfold hessian
    rw [hgrad]
  have havLH : A2 V LH := ⟨by rw [hhess]; exact hHess⟩
  have hprob : av.targetProbability = a.targetProbability := Subtype.ext hπ
  have hTI : TalagrandBound av := by
    intro μ hKL
    rw [hprob]
    change (QuadraticTransport.cost μ a.targetProbability).toReal / 2 ≤
      (klDiv (μ : Measure E) πv).toReal/m
    rw [hπ]
    have hk : klDiv (μ : Measure E) π ≠ ∞ := by
      change klDiv (μ : Measure E) πv ≠ ∞ at hKL
      rwa [hπ] at hKL
    have hle := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hTal μ hk)
    rw [ENNReal.toReal_ofReal (by positivity)] at hle
    have hident : 2*(klDiv (μ : Measure E) π).toReal/m =
      2*((klDiv (μ : Measure E) π).toReal/m) := by ring
    rw [hident] at hle
    change (QuadraticTransport.cost μ a.targetProbability).toReal ≤
      2*((klDiv (μ : Measure E) π).toReal/m) at hle
    linarith only [hle]
  have hacv : ν ≪ πv := hπ.symm ▸ hac
  let f (x : E) := (ν.rnDeriv π x).toReal
  let fv (x : E) := (ν.rnDeriv πv x).toReal
  have hLv : MemLp fv 2 πv := by simpa only [fv,hπ] using hL2
  have hsqu : ‖hL2.toLp f‖^2 = ∫ x, (f x)^2 ∂π := by
    rw [realLp_norm_sq]
    exact integral_congr_ae (hL2.coeFn_toLp.mono fun _ hx => congrArg (·^2) hx)
  have hsqv : ‖hLv.toLp fv‖^2 = ∫ x, (fv x)^2 ∂πv := by
    rw [realLp_norm_sq]
    exact integral_congr_ae (hLv.coeFn_toLp.mono fun _ hx => congrArg (·^2) hx)
  have hwv : ‖hLv.toLp fv‖ ≤ M := by
    apply (sq_le_sq₀ (norm_nonneg _) (by linarith only [hM])).mp
    rw [hsqv]
    change (∫ x,(ν.rnDeriv πv x).toReal^2 ∂πv) ≤ _
    rw [hπ]
    exact hsqu ▸ (sq_le_sq₀ (norm_nonneg _) (by linarith only [hM])).mpr hwarm
  have hlog : 0 ≤ Real.log (2*M/ε) :=
    Real.log_nonneg ((one_le_div hε).mpr (by linarith only [hM,hε₁]))
  have hnit := (mul_le_mul_of_nonneg_right (upperC₂_law_bound ρ hρ) hlog).trans hn
  have hmixed := theoremOne_explicit_normalized hPP av hLH havLH hTI hmin ρ hρ ν
    hacv hM hε hε₁ hLv hwv N n hN hnit
  dsimp only at hmixed
  let h := 4/((N:ℝ)*Real.sqrt m)
  let hUm := hU.continuous.measurable
  let hg := hLip.continuous.measurable
  let hVm := av.twice_contDiff.continuous.measurable
  let hgv := (contDiff_gradient_of_twice_contDiff V av.twice_contDiff).continuous.measurable
  have hP : roundedVerletKernel V hVm (gradient V) hgv h ρ =
      roundedVerletKernel U hUm (gradient U) hg h ρ :=
    (roundedVerletKernel_congr_gradient V hVm hgv hg h ρ hgrad).trans
      (roundedVerletKernel_sub_const U hUm (gradient U) hg u₀ h ρ)
  change totalVariation (evolve (fun _ => roundedVerletKernel V hVm (gradient V) hgv h ρ) ν n)
    πv ≤ ENNReal.ofReal ε at hmixed
  rwa [hP,hπ] at hmixed

end BreakingResonance

#print axioms BreakingResonance.theoremOne
