import BreakingResonance.ReferenceConductance
import BreakingResonance.RoundedHorizon

noncomputable section

open MeasureTheory ProbabilityTheory Set PersistencePays
open scoped ENNReal ProbabilityTheory Gradient

namespace BreakingResonance

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Proposition C for a Fourier comparison constant and a duration cutoff
satisfying the conditions in Section 3. -/
theorem propositionC (hPP : PPInterpolation E)
    {U : E → ℝ} {m L LH : ℝ} (a : A1 U m L) (hLH : 0 ≤ LH) (hlip : A2 U LH)
    (hTI : TalagrandBound a) (hmin : U a.minimizer = 0)
    (ρ : Measure ℝ) [IsProbabilityMeasure ρ] {bρ δρ : ℝ}
    (hρ : NonresonantDuration ρ m bρ δρ)
    {τstar : ℝ} (hτ : 0 < τstar) (hcut : (ρ (Ioi τstar)).toReal ≤ δρ/4)
    {c s R : ℝ} (hc : 0 < c) (hc₁ : c ≤ 1) (hs : 0 < s) (_hs₁ : s ≤ 1/2)
    (hR : 1 ≤ R) (N : ℕ) (hN : 1 ≤ N) (_hNδ : 16/Real.sqrt δρ ≤ (N:ℝ))
    (hcompare : ∀ θ ∈ Icc (-Real.pi) Real.pi,
      let h := 4/((N:ℝ)*Real.sqrt m)
      c*(1-cosineSeries (countLawWeight (triangularCountLaw h N)) θ) ≤
        1-cosineSeries (countLawWeight (roundedDurationLaw h (conditionalDurationLaw ρ τstar))) θ)
    (htail : (phaseGibbs U).real {z | R < phaseEnergy U z} ≤ (c/600)*s)
    (hbudget : let h := 4/((N:ℝ)*Real.sqrt m)
       let Tstar := τstar+4/Real.sqrt m
       h^2*(L*R+LH*Tstar*R*Real.sqrt R) ≤ (c/600)/3) :
    let h := 4/((N:ℝ)*Real.sqrt m)
    let hU := a.twice_contDiff.continuous.measurable
    let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
    RestrictedConductance (positionGibbs U) (roundedVerletKernel U hU (gradient U) hg h ρ) s
      ((ρ (Iic τstar)).toReal*c/60) := by
  dsimp only
  let h : ℝ := 4/((N:ℝ)*Real.sqrt m)
  let Tstar := τstar+4/Real.sqrt m
  let η := c/600
  let g := gradient U
  let hU := a.twice_contDiff.continuous.measurable
  let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
  let q := triangularCountLaw h N
  let w := roundedDurationLaw h (conditionalDurationLaw ρ τstar)
  have hη : 0 < η := div_pos hc (by norm_num)
  have hη₁ : η ≤ 1/600 := div_le_div_of_nonneg_right hc₁ (by norm_num)
  have hNp : 0 < N := by omega
  have hNr : 0 < (N:ℝ) := by exact_mod_cast hNp
  have hsqrt : 0 < Real.sqrt m := Real.sqrt_pos.mpr a.m_pos
  have hh : 0 < h := div_pos (by norm_num) (mul_pos hNr hsqrt)
  have hT : (N:ℝ)*h = 4/Real.sqrt m := by dsimp [h]; field_simp
  have hTstar : (N:ℝ)*h ≤ Tstar := by rw [hT]; dsimp [Tstar]; linarith only [hτ]
  have hround : τstar+h ≤ Tstar := by
    have hn : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
    have hm := mul_le_mul_of_nonneg_right hn hh.le
    dsimp [Tstar]
    linarith only [hm,hT]
  have hpc := retainedDuration_ne_zero ρ τstar hρ.gap_le_one hcut
  let : IsProbabilityMeasure (positionGibbs U) := a.gibbs_isProbabilityMeasure
  let : IsProbabilityMeasure (conditionalDurationLaw ρ τstar) :=
    conditionalDuration_isProbability ρ τstar hpc
  let : IsProbabilityMeasure q := triangularCount_probability hh hNp
  have haenergy := ppModifiedEnergy_of_hessian a.twice_contDiff hlip
  have href := triangular_reference_conductance hPP a hLH hlip haenergy hTI hmin hh hR hs
    hη hη₁ N hNp hT hTstar hbudget htail
  apply transfer_restricted_conductance U hU a.gibbs_integrable g hg h ρ τstar hpc q hc hcompare href
  intro A hA hsA hAh
  have hl : ∀ᵐ j : ℕ ∂w, (j:ℝ)*h ≤ Tstar :=
    conditional_count_horizon hh hρ.positive_ae hround
  have ht : 0 ≤ Tstar := (by positivity : 0 ≤ (N:ℝ)*h).trans hTstar
  have hacc : ∀ᵐ j : ℕ ∂w, ∀ z : E×E, phaseEnergy U z ≤ R →
        ENNReal.ofReal (1-η) ≤ acceptProbability
          (fun z => phaseEnergy U z-phaseEnergy U (trajectory g h z j)) z :=
    hl.mono fun j hj z hz => shell_acceptance a hmin hLH haenergy hh ht hR hη.le
      (hη₁.trans (by norm_num)) hbudget j hj z hz
  have he := rejection_on_shell_mixture U hU a.gibbs_integrable g hg h w hη.le
    (hη₁.trans (by norm_num)) hacc hA
  have hsA' : s ≤ (positionGibbs U).real A := by
    have hm := ENNReal.toReal_mono (measure_ne_top (positionGibbs U) A) hsA
    rwa [ENNReal.toReal_ofReal hs.le] at hm
  have hm := mul_le_mul_of_nonneg_left hsA' hη.le
  change (phaseGibbs U).real {z | R < phaseEnergy U z} ≤ η*s at htail
  change _ ≤ (c/300)*(positionGibbs U).real A
  calc
    _ ≤ η*(positionGibbs U).real A+(phaseGibbs U).real {z | R < phaseEnergy U z} := he
    _ ≤ 2*η*(positionGibbs U).real A := by linarith only [hm,htail]
    _ = _ := by dsimp [η]; ring

end BreakingResonance

#print axioms BreakingResonance.propositionC
