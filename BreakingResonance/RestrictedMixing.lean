import BreakingResonance.BoundedDensityDecay
import BreakingResonance.WarmDensityTruncation

noncomputable section

open MeasureTheory Set ProbabilityTheory PersistencePays
open scoped ProbabilityTheory ENNReal

namespace BreakingResonance

variable {S : Type*} [MeasurableSpace S]

theorem markov_evolve_mono (P : Kernel S S) (μ ν : Measure S) (h : μ ≤ ν) :
    ∀ n, evolve (fun _ => P) μ n ≤ evolve (fun _ => P) ν n := by
  intro n
  induction n with
  | zero => exact h
  | succ n ih =>
    rw [evolve_succ,evolve_succ]
    apply Measure.le_iff.mpr
    intro A hA
    rw [Measure.bind_apply hA P.aemeasurable,Measure.bind_apply hA P.aemeasurable]
    exact lintegral_mono' ih le_rfl

theorem markov_evolve_univ (P : Kernel S S) [IsMarkovKernel P] (μ : Measure S) :
    ∀ n, (evolve (fun _ => P) μ n) univ = μ univ := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [evolve_succ,Measure.bind_apply MeasurableSet.univ P.aemeasurable]
    simpa only [measure_univ,lintegral_const,one_mul] using ih

/-- Proposition A, with the restricted conductance and lower spectral
inequalities stated for the actual Markov kernel. -/
theorem propositionA
    (π : Measure S) [IsProbabilityMeasure π] (P : Kernel S S) [IsMarkovKernel P]
    (hrev : P.IsReversible π) {s φP βP : ℝ} (hs : 0 < s) (_hs₁ : s ≤ 1/2)
    (hφ : 0 < φP) (hφ₁ : φP ≤ 1) (hβ : 0 < βP) (hβ₁ : βP ≤ 1)
    (hcond : RestrictedConductance π P s φP)
    (hspec : ∀ f : Lp ℝ 2 π,
      βP*markovDirichlet π P f ≤ ‖f‖^2-‖markovL2 π P hrev.invariant f‖^2)
    (ν : Measure S) [IsProbabilityMeasure ν] (hac : ν ≪ π)
    {M : ℝ} (hL2 : MemLp (fun x => (ν.rnDeriv π x).toReal) 2 π)
    (hM : ‖hL2.toLp (fun x => (ν.rnDeriv π x).toReal)‖ ≤ M)
    {ε : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1) (k : ℕ) :
    let Mcap := 4*M^2/ε
    totalVariation (evolve (fun _ => P) ν k) π ≤ ENNReal.ofReal
      (ε/2+(1/2)*Real.sqrt (Real.exp (-(k:ℝ)*βP*φP^2/2)*Mcap+2*s*Mcap^2)) := by
  let C := 4*M^2/ε
  let u (x : S) := (ν.rnDeriv π x).toReal
  have hu : ‖hL2.toLp u‖^2 = ∫ x, (u x)^2 ∂π := by
    rw [realLp_norm_sq]
    exact integral_congr_ae (hL2.coeFn_toLp.mono fun _ hx => congrArg (·^2) hx)
  have hMsq : (∫ x, (u x)^2 ∂π) ≤ M^2 := hu ▸
    (sq_le_sq₀ (norm_nonneg _) ((norm_nonneg _).trans hM)).mpr hM
  have hM₀ : 0 ≤ M := (norm_nonneg _).trans hM
  obtain ⟨f,hf,h0,hC,hmean,ξ,hξν,hξf,hξ⟩ :=
    warm_density_truncation ν π hac hM₀ hε hε₁ ((Real.sqrt_le_left hM₀).mpr hMsq) hL2
  let μ := π.withDensity (ENNReal.ofReal ∘ f)
  have hfi := markovAction_integrable_bound (π := π) hf h0 hC
  have : IsProbabilityMeasure μ := by
    constructor
    change (π.withDensity (ENNReal.ofReal ∘ f)) univ = 1
    rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
    change (∫⁻ x, ENNReal.ofReal (f x) ∂π) = 1
    rw [← ofReal_integral_eq_lintegral_ofReal hfi (Filter.Eventually.of_forall h0),hmean]
    norm_num
  have hdist := totalVariation_le_of_common_submeasure
    (evolve (fun _ => P) ν k) (evolve (fun _ => P) μ k) (evolve (fun _ => P) ξ k)
    (markov_evolve_mono P _ _ hξν k) (markov_evolve_mono P _ _ hξf k)
  have hd : totalVariation (evolve (fun _ => P) ν k) (evolve (fun _ => P) μ k) ≤
      ENNReal.ofReal (ε/2) := by
    refine hdist.trans (ENNReal.ofReal_le_ofReal ?_)
    change 1-((evolve (fun _ => P) ξ k) univ).toReal ≤ ε/2
    rw [markov_evolve_univ]
    change 1-ξ.real univ ≤ ε/2
    linarith only [hξ]
  let F := densityIterate P f k
  have hF := densityIterate_bounded P hf h0 hC k
  have hL2F : MemLp F 2 π := memLp_of_bounded
    (Filter.Eventually.of_forall fun x => ⟨hF.2.1 x,hF.2.2 x⟩) hF.1.aestronglyMeasurable 2
  have hmF : (∫ x, F x ∂π) = 1 :=
    (densityIterate_integral_eq π P hrev.invariant hf h0 hC k).trans hmean
  have hv := bounded_density_decay π P hrev hs.le hβ.le hβ₁ hφ hφ₁ hcond
    hspec hf h0 hC hmean k
  have htv : totalVariation (evolve (fun _ => P) μ k) π ≤ ENNReal.ofReal
      ((1/2)*Real.sqrt (Real.exp (-(k:ℝ)*βP*φP^2/2)*C+2*s*C^2)) := by
    rw [reversible_evolve_density π P hrev hf h0 hC]
    refine (density_totalVariation_le_l2 π hF.1 hL2F hF.2.1 hmF).trans ?_
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hv) (by norm_num))
  change _ ≤ ENNReal.ofReal (ε/2+(1/2)*Real.sqrt (_+2*s*C^2))
  have htri := (totalVariation_triangle (evolve (fun _ => P) ν k)
    (evolve (fun _ => P) μ k) π).trans (add_le_add hd htv)
  rwa [← ENNReal.ofReal_add (by positivity) (by positivity)] at htri

end BreakingResonance

#print axioms BreakingResonance.propositionA
