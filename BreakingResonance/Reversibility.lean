import BreakingResonance.RandomizedKernel
import BreakingResonance.MetropolisFlow
import BreakingResonance.RoundingCost
import PersistencePays.PhaseGibbsDensity

/-! Reversibility of the actual endpoint Metropolis position kernel. -/
namespace BreakingResonance
noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory ProbabilityTheory Set PersistencePays
open scoped ENNReal ProbabilityTheory

section General
variable {S V : Type*} [MeasurableSpace S] [MeasurableSpace V]

theorem proposalKernel_flow_integral (Q : S × V → S) (hQ : Measurable Q)
    (G : S × V → ℝ) (hG : Measurable G) (ν : Measure V) [IsProbabilityMeasure ν]
    (π : Measure S) [SFinite π] (A B : Set S) (hA : MeasurableSet A)
    (hB : MeasurableSet B) :
    (∫⁻ x in A, proposalKernel Q hQ G hG ν x B ∂π) =
      ∫⁻ z : S × V, A.indicator (fun _ => 1) z.1 *
        (metropolisDecisionKernel Q hQ G hG z B) ∂π.prod ν := by
  have hm : Measurable (fun z : S × V => A.indicator (fun _ => (1 : ℝ≥0∞)) z.1) :=
    (measurable_const.indicator hA).comp measurable_fst
  rw [lintegral_prod _ (hm.fun_mul ((metropolisDecisionKernel Q hQ G hG).measurable_coe hB)).aemeasurable]
  rw [← lintegral_indicator hA]
  apply lintegral_congr
  intro x
  by_cases hx : x ∈ A
  · simp only [indicator_of_mem hx, one_mul]
    rw [proposalKernel_apply Q hQ G hG ν x B hB]
    apply lintegral_congr
    intro v
    simp [metropolisDecisionKernel, Measure.dirac_apply' _ hB, smul_eq_mul]
    rfl
  · simp [hx]

theorem proposalKernel_flow_split (Q : S × V → S) (hQ : Measurable Q)
    (G : S × V → ℝ) (hG : Measurable G) (ν : Measure V) [IsProbabilityMeasure ν]
    (π : Measure S) [SFinite π] (A B : Set S) (hA : MeasurableSet A)
    (hB : MeasurableSet B) :
    (∫⁻ x in A, proposalKernel Q hQ G hG ν x B ∂π) =
      (∫⁻ z : S × V, A.indicator (fun _ => 1) z.1 *
        B.indicator (fun _ => 1) (Q z) ∂(π.prod ν).withDensity (acceptProbability G)) +
      (∫⁻ z : S × V, A.indicator (fun _ => 1) z.1 *
        B.indicator (fun _ => 1) z.1 ∂(π.prod ν).withDensity (fun z => 1-acceptProbability G z)) := by
  have hm : Measurable (acceptProbability G) :=
    (measurable_const.min hG.exp).ennreal_ofReal
  have hn : Measurable (fun z => 1-acceptProbability G z) := by
    exact measurable_const.sub hm
  have ha : Measurable (fun z : S × V => A.indicator (fun _ => (1 : ℝ≥0∞)) z.1) :=
    (measurable_const.indicator hA).comp measurable_fst
  have hb : Measurable (fun z => B.indicator (fun _ => (1 : ℝ≥0∞)) (Q z)) :=
    (measurable_const.indicator hB).comp hQ
  have hb' : Measurable (fun z : S × V => B.indicator (fun _ => (1 : ℝ≥0∞)) z.1) :=
    (measurable_const.indicator hB).comp measurable_fst
  rw [proposalKernel_flow_integral Q hQ G hG ν π A B hA hB,
    lintegral_withDensity_eq_lintegral_mul _ hm (ha.fun_mul hb),
    lintegral_withDensity_eq_lintegral_mul _ hn (ha.fun_mul hb')]
  rw [← lintegral_add_left (hm.mul (ha.fun_mul hb))]
  apply lintegral_congr
  intro z
  simp only [metropolisDecisionKernel, Kernel.coe_mk, Measure.add_apply,
    Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ hB]
  change _ = acceptProbability G z * (_ * _) + (1-acceptProbability G z)*(_*_)
  ring
  rfl

theorem proposalKernel_reversible_of_acceptedMeasure
    (Q : S × V → S) (hQ : Measurable Q) (G : S × V → ℝ) (hG : Measurable G)
    (ν : Measure V) [IsProbabilityMeasure ν] (π : Measure S) [SFinite π]
    (T : (S × V) ≃ᵐ (S × V)) (hT : Function.Involutive T)
    (hQobs : ∀ z, Q z = (T z).1)
    (hinv : ((π.prod ν).withDensity (acceptProbability G)).map T =
      (π.prod ν).withDensity (acceptProbability G)) :
    Kernel.IsReversible (proposalKernel Q hQ G hG ν) π := by
  intro A B hA hB
  rw [proposalKernel_flow_split Q hQ G hG ν π A B hA hB,
    proposalKernel_flow_split Q hQ G hG ν π B A hB hA]
  congr 1
  · nth_rw 1 [← hinv]
    rw [lintegral_map (by fun_prop) T.measurable]
    apply lintegral_congr
    intro z
    rw [hQobs, hT, hQobs]
    exact mul_comm _ _
  · apply lintegral_congr
    intro z
    exact mul_comm _ _

end General

section Mixture
variable {S : Type*} [MeasurableSpace S]

theorem reversible_countable_mixture (K : ℕ → Kernel S S) (P : Kernel S S)
    (π : Measure S) [SFinite π] (w : Measure ℕ) [SFinite w]
    (hmix : ∀ x A, MeasurableSet A → P x A = ∫⁻ j, K j x A ∂w)
    (hrev : ∀ j, Kernel.IsReversible (K j) π) : Kernel.IsReversible P π := by
  have hjoint (A : Set S) (hA : MeasurableSet A) :
      Measurable (fun z : S × ℕ => K z.2 z.1 A) := by
    apply measurable_from_prod_countable_left
    intro j
    exact (K j).measurable_coe hA
  intro A B hA hB
  simp_rw [hmix _ _ hB, hmix _ _ hA]
  calc
    _ = ∫⁻ j, ∫⁻ x in A, K j x B ∂π ∂w :=
      lintegral_lintegral_swap (hjoint B hB).aemeasurable
    _ = ∫⁻ j, ∫⁻ x in B, K j x A ∂π ∂w := by
      apply lintegral_congr
      intro j
      exact hrev j hA hB
    _ = _ := (lintegral_lintegral_swap (hjoint A hA).aemeasurable).symm
end Mixture

section Density
variable {Z : Type*} [MeasurableSpace Z]

omit [MeasurableSpace Z] in
theorem gibbs_acceptance_identity (H : Z → ℝ) (T : Z → Z) (z : Z) :
    ENNReal.ofReal (Real.exp (-H z)) * ENNReal.ofReal (min 1 (Real.exp (H z-H (T z)))) =
      min (ENNReal.ofReal (Real.exp (-H z))) (ENNReal.ofReal (Real.exp (-H (T z)))) := by
  rw [ENNReal.ofReal_min, ENNReal.ofReal_one, mul_min, mul_one]
  congr 1
  rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
  congr 2
  ring

theorem gibbs_acceptedMeasure_invariant (μ : Measure Z) [NeZero μ]
    (H : Z → ℝ) (hH : Measurable H) (hi : Integrable (fun z => Real.exp (-H z)) μ)
    (T : Z ≃ᵐ Z) (hT : Function.Involutive T) (hmp : MeasurePreserving T μ μ) :
    ((μ.tilted (-H)).withDensity
      (fun z => ENNReal.ofReal (min 1 (Real.exp (H z-H (T z)))))).map T =
    (μ.tilted (-H)).withDensity
      (fun z => ENNReal.ofReal (min 1 (Real.exp (H z-H (T z))))) := by
  have hp : Measurable (fun z => ENNReal.ofReal (Real.exp (-H z))) := by fun_prop
  have hα : Measurable (fun z => ENNReal.ofReal (min 1 (Real.exp (H z-H (T z))))) := by fun_prop
  rw [tilted_eq_smul_gibbs μ H hH hi, withDensity_smul_measure,
    ← withDensity_mul μ hp hα]
  have he : (fun z => ENNReal.ofReal (Real.exp (-H z))) *
      (fun z => ENNReal.ofReal (min 1 (Real.exp (H z-H (T z))))) =
      acceptedWeight (fun z => ENNReal.ofReal (Real.exp (-H z))) T := by
    funext z
    exact gibbs_acceptance_identity H T z
  rw [he, Measure.map_smul]
  rw [acceptedMeasure_invariant μ _ hp T hT hmp]
end Density

section Verlet
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem measurable_phaseEnergy (U : E → ℝ) (hU : Measurable U) :
    Measurable (phaseEnergy U) := by unfold phaseEnergy; fun_prop

def fixedVerletKernel (U : E → ℝ) (hU : Measurable U)
    (g : E → E) (hg : Measurable g) (h : ℝ) (j : ℕ) : Kernel E E :=
  proposalKernel (fun z => (trajectory g h z j).1)
    (trajectory_measurePreserving g hg h j).measurable.fst
    (fun z => phaseEnergy U z - phaseEnergy U (trajectory g h z j))
    ((measurable_phaseEnergy U hU).sub ((measurable_phaseEnergy U hU).comp
      (trajectory_measurePreserving g hg h j).measurable)) (stdGaussian E)

instance fixedVerletKernel_markov (U : E → ℝ) (hU : Measurable U)
    (g : E → E) (hg : Measurable g) (h : ℝ) (j : ℕ) :
    IsMarkovKernel (fixedVerletKernel U hU g hg h j) := by
  unfold fixedVerletKernel
  infer_instance

theorem fixedVerletKernel_reversible (U : E → ℝ) (hU : Measurable U)
    (hi : Integrable (fun x => Real.exp (-U x)) volume)
    (g : E → E) (hg : Measurable g) (h : ℝ) (j : ℕ) :
    Kernel.IsReversible (fixedVerletKernel U hU g hg h j) (positionGibbs U) := by
  unfold fixedVerletKernel
  apply proposalKernel_reversible_of_acceptedMeasure _ _ _ _ _ _
    (flippedTrajectoryEquiv g hg h j) (flipped_trajectory_involutive g h j)
  · intro z; rfl
  · change ((phaseGibbs U).withDensity _).map _ = (phaseGibbs U).withDensity _
    have hα : acceptProbability
        (fun z => phaseEnergy U z-phaseEnergy U (trajectory g h z j)) =
        fun z => ENNReal.ofReal (min 1 (Real.exp (phaseEnergy U z-
          phaseEnergy U (flippedTrajectoryEquiv g hg h j z)))) := by
      funext z
      change ENNReal.ofReal (min 1 (Real.exp (phaseEnergy U z-phaseEnergy U (trajectory g h z j)))) =
        ENNReal.ofReal (min 1 (Real.exp (phaseEnergy U z-phaseEnergy U (velocityFlip (trajectory g h z j)))))
      rw [phaseEnergy_velocityFlip]
    rw [hα, phaseGibbs_eq_tilted U hU hi]
    exact gibbs_acceptedMeasure_invariant _ (phaseEnergy U) (measurable_phaseEnergy U hU)
      (phase_gibbs_integrable U hi) (flippedTrajectoryEquiv g hg h j)
      (flipped_trajectory_involutive g h j) (flipped_trajectory_measurePreserving g hg h j)

theorem randomizedVerletKernel_mixture (U : E → ℝ) (hU : Measurable U)
    (g : E → E) (hg : Measurable g) (h : ℝ) (lawJ : Measure ℕ)
    [IsProbabilityMeasure lawJ] (x : E) (A : Set E) (hA : MeasurableSet A) :
    randomizedVerletKernel U hU g hg h lawJ x A =
      ∫⁻ j, fixedVerletKernel U hU g hg h j x A ∂lawJ := by
  unfold randomizedVerletKernel
  rw [proposalKernel_apply _ _ _ _ _ x A hA]
  have hα : Measurable (fun z : ℕ × E => acceptProbability (verletLogAcceptance U g h) (x,z)) :=
    ((measurable_const.min (measurable_verletLogAcceptance U hU g hg h).exp).ennreal_ofReal).comp
      (measurable_const.prodMk measurable_id)
  have hq : Measurable (fun z : ℕ × E => verletProposal g h (x,z)) :=
    (measurable_verletProposal g hg h).comp (measurable_const.prodMk measurable_id)
  have hf : Measurable (fun z : ℕ × E =>
      acceptProbability (verletLogAcceptance U g h) (x,z) * A.indicator (fun _ => 1) (verletProposal g h (x,z)) +
      (1-acceptProbability (verletLogAcceptance U g h) (x,z)) * A.indicator (fun _ => 1) x) := by
    exact (hα.fun_mul ((measurable_const.indicator hA).comp hq)).fun_add
      ((measurable_const.sub hα).mul measurable_const)
  rw [lintegral_prod _ hf.aemeasurable]
  apply lintegral_congr
  intro j
  rw [fixedVerletKernel, proposalKernel_apply _ _ _ _ _ x A hA]
  rfl

theorem randomizedVerletKernel_reversible (U : E → ℝ) (hU : Measurable U)
    (hi : Integrable (fun x => Real.exp (-U x)) volume)
    (g : E → E) (hg : Measurable g) (h : ℝ) (lawJ : Measure ℕ)
    [IsProbabilityMeasure lawJ] :
    Kernel.IsReversible (randomizedVerletKernel U hU g hg h lawJ) (positionGibbs U) :=
  reversible_countable_mixture (fixedVerletKernel U hU g hg h) _ _ lawJ
    (randomizedVerletKernel_mixture U hU g hg h lawJ)
    (fixedVerletKernel_reversible U hU hi g hg h)

theorem roundedVerletKernel_reversible (U : E → ℝ) (hU : Measurable U)
    (hi : Integrable (fun x => Real.exp (-U x)) volume)
    (g : E → E) (hg : Measurable g) (h : ℝ) (ρ : Measure ℝ)
    [IsProbabilityMeasure ρ] :
    Kernel.IsReversible (roundedVerletKernel U hU g hg h ρ) (positionGibbs U) :=
  randomizedVerletKernel_reversible U hU hi g hg h (roundedDurationLaw h ρ)

theorem roundedVerletKernel_invariant (U : E → ℝ) (hU : Measurable U)
    (hi : Integrable (fun x => Real.exp (-U x)) volume)
    (g : E → E) (hg : Measurable g) (h : ℝ) (ρ : Measure ℝ)
    [IsProbabilityMeasure ρ] :
    Kernel.Invariant (roundedVerletKernel U hU g hg h ρ) (positionGibbs U) :=
  (roundedVerletKernel_reversible U hU hi g hg h ρ).invariant

/-- Lemma 5.1. The kernels with a fixed number of Verlet steps and all
their state-independent mixtures are reversible for the position Gibbs law. -/
theorem verlet_gradient_reversibility (U : E → ℝ) (hU : ContDiff ℝ 1 U)
    (hi : Integrable (fun x => Real.exp (-U x)) volume) (h : ℝ) :
    let hUg := hU.continuous.measurable
    let hg : Measurable (gradient U) := by
      have hd : ContDiff ℝ 0 (gradient U) := by
        unfold gradient
        exact (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.contDiff.comp
          (hU.fderiv_right (by norm_num))
      exact hd.continuous.measurable
    (∀ j : ℕ, Kernel.IsReversible (fixedVerletKernel U hUg (gradient U) hg h j)
      (positionGibbs U)) ∧
    (∀ (lawJ : ProbabilityMeasure ℕ),
      Kernel.IsReversible (randomizedVerletKernel U hUg (gradient U) hg h lawJ)
        (positionGibbs U)) := by
  dsimp only
  exact ⟨fixedVerletKernel_reversible U _ hi _ _ h,
    fun lawJ => randomizedVerletKernel_reversible U _ hi _ _ h lawJ⟩
end Verlet
end
end BreakingResonance
