import BreakingResonance.VerletTrajectory
import BreakingResonance.RejectionBounds
import PersistencePays.GaussianBridgeLaw

/-! The actual endpoint Metropolis decision, fresh auxiliary randomness,
and the randomized Verlet position kernel. This file constructs probability
kernels; their Gibbs reversibility remains a separate proof obligation. -/
namespace BreakingResonance
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

section General
variable {S V : Type*} [MeasurableSpace S] [MeasurableSpace V]

def acceptProbability (G : S × V → ℝ) (z : S × V) : ℝ≥0∞ :=
  ENNReal.ofReal (min 1 (Real.exp (G z)))

omit [MeasurableSpace S] [MeasurableSpace V] in
theorem acceptProbability_le_one (G : S × V → ℝ) (z : S × V) :
    acceptProbability G z ≤ 1 := by
  simp [acceptProbability]

def metropolisDecisionKernel (Q : S × V → S) (hQ : Measurable Q)
    (G : S × V → ℝ) (hG : Measurable G) : Kernel (S × V) S where
  toFun z := acceptProbability G z • Measure.dirac (Q z) +
    (1 - acceptProbability G z) • Measure.dirac z.1
  measurable' := by
    have hm : Measurable (acceptProbability G) :=
      (measurable_const.min hG.exp).ennreal_ofReal
    apply Measure.measurable_of_measurable_coe
    intro A hA
    simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
    exact (hm.mul ((Kernel.deterministic Q hQ).measurable_coe hA)).add
      ((measurable_const.sub hm).mul
        ((Kernel.deterministic Prod.fst measurable_fst).measurable_coe hA))

instance metropolisDecisionKernel_markov (Q : S × V → S) (hQ : Measurable Q)
    (G : S × V → ℝ) (hG : Measurable G) :
    IsMarkovKernel (metropolisDecisionKernel Q hQ G hG) where
  isProbabilityMeasure z := by
    constructor
    change (acceptProbability G z • Measure.dirac (Q z) +
      (1 - acceptProbability G z) • Measure.dirac z.1) univ = 1
    simp only [Measure.add_apply, Measure.smul_apply, Measure.dirac_apply_of_mem (mem_univ _),
      smul_eq_mul, mul_one]
    exact add_tsub_cancel_of_le (acceptProbability_le_one G z)

def proposalKernel (Q : S × V → S) (hQ : Measurable Q)
    (G : S × V → ℝ) (hG : Measurable G) (ν : Measure V) : Kernel S S :=
  metropolisDecisionKernel Q hQ G hG ∘ₖ (Kernel.id ×ₖ Kernel.const S ν)

instance proposalKernel_markov (Q : S × V → S) (hQ : Measurable Q)
    (G : S × V → ℝ) (hG : Measurable G) (ν : Measure V) [IsProbabilityMeasure ν] :
    IsMarkovKernel (proposalKernel Q hQ G hG ν) := by
  unfold proposalKernel
  infer_instance

theorem proposalKernel_apply (Q : S × V → S) (hQ : Measurable Q)
    (G : S × V → ℝ) (hG : Measurable G) (ν : Measure V) [IsProbabilityMeasure ν]
    (x : S) (A : Set S) (hA : MeasurableSet A) :
    proposalKernel Q hQ G hG ν x A =
      ∫⁻ v, acceptProbability G (x,v) * A.indicator (fun _ => 1) (Q (x,v)) +
        (1-acceptProbability G (x,v)) * A.indicator (fun _ => 1) x ∂ν := by
  rw [proposalKernel, Kernel.comp_apply' _ _ _ hA, Kernel.prod_apply]
  change (∫⁻ z, metropolisDecisionKernel Q hQ G hG z A ∂(Measure.dirac x).prod ν) = _
  rw [lintegral_prod _ ((metropolisDecisionKernel Q hQ G hG).measurable_coe hA).aemeasurable]
  rw [lintegral_dirac' _ (Measurable.lintegral_prod_right
    ((metropolisDecisionKernel Q hQ G hG).measurable_coe hA))]
  apply lintegral_congr
  intro v
  simp [metropolisDecisionKernel, Measure.dirac_apply' _ hA, smul_eq_mul]
  rfl

theorem proposalKernel_stays (Q : S × V → S) (hQ : Measurable Q)
    (G : S × V → ℝ) (hG : Measurable G) (ν : Measure V) [IsProbabilityMeasure ν]
    (x : S) (A : Set S) (hA : MeasurableSet A) (hx : x ∈ A) :
    1 - (∫⁻ v, acceptProbability G (x,v) ∂ν) ≤ proposalKernel Q hQ G hG ν x A := by
  have hm : Measurable (fun v => acceptProbability G (x,v)) :=
    (measurable_const.min ((hG.comp (measurable_const.prodMk measurable_id)).exp)).ennreal_ofReal
  have hsum : (∫⁻ v, acceptProbability G (x,v) ∂ν) +
      (∫⁻ v, 1-acceptProbability G (x,v) ∂ν) = 1 := by
    rw [← lintegral_add_left hm]
    simp [add_tsub_cancel_of_le (acceptProbability_le_one G _)]
  have hlow : (∫⁻ v, 1-acceptProbability G (x,v) ∂ν) ≤
      proposalKernel Q hQ G hG ν x A := by
    rw [proposalKernel_apply Q hQ G hG ν x A hA]
    apply lintegral_mono
    intro v
    simp only [indicator_of_mem hx, mul_one]
    exact le_add_left le_rfl
  calc
    1 - (∫⁻ v, acceptProbability G (x,v) ∂ν) ≤
      ∫⁻ v, 1-acceptProbability G (x,v) ∂ν := by
        exact tsub_le_iff_right.mpr (by rw [add_comm]; exact le_of_eq hsum.symm)
    _ ≤ _ := hlow

theorem proposalKernel_retains (Q : S × V → S) (hQ : Measurable Q)
    (G : S × V → ℝ) (hG : Measurable G) (ν : Measure V) [IsProbabilityMeasure ν]
    (x : S) (A : Set S) (hA : MeasurableSet A) (hx : x ∈ A)
    (a : ℝ) (ha : 0 ≤ a)
    (hacc : (∫⁻ v, acceptProbability G (x,v) ∂ν) ≤ ENNReal.ofReal a) :
    ENNReal.ofReal (1-a) ≤ proposalKernel Q hQ G hG ν x A := by
  rw [ENNReal.ofReal_sub 1 ha, ENNReal.ofReal_one]
  exact (tsub_le_tsub_left hacc 1).trans (proposalKernel_stays Q hQ G hG ν x A hA hx)

theorem proposalKernel_totalVariation_lower (Q : S × V → S) (hQ : Measurable Q)
    (G : S × V → ℝ) (hG : Measurable G) (ν : Measure V) [IsProbabilityMeasure ν]
    (μ π : Measure S) [IsProbabilityMeasure μ] [IsProbabilityMeasure π]
    (A E : Set S) (hA : MeasurableSet A) (hE : MeasurableSet E) (hEA : E ⊆ A)
    (hπ : π.real A = 1/2) (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hstart : 1-b ≤ μ.real E)
    (hacc : ∀ x ∈ E, (∫⁻ v, acceptProbability G (x,v) ∂ν) ≤ ENNReal.ofReal a)
    (n : ℕ) :
    ENNReal.ofReal (1/2-b-(n : ℝ)*a) ≤
      totalVariation (PersistencePays.evolve (fun _ => proposalKernel Q hQ G hG ν) μ n) π := by
  exact rejection_totalVariation_lower (proposalKernel Q hQ G hG ν) μ π A E
    hA hE hEA hπ a b ha ha1 hstart
    (fun x hx => proposalKernel_retains Q hQ G hG ν x E hE hx a ha (hacc x hx)) n
end General

section Verlet
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
open PersistencePays

def verletProposal (g : E → E) (h : ℝ) (z : E × (ℕ × E)) : E :=
  (trajectory g h (z.1,z.2.2) z.2.1).1

def verletLogAcceptance (U : E → ℝ) (g : E → E) (h : ℝ)
    (z : E × (ℕ × E)) : ℝ :=
  phaseEnergy U (z.1,z.2.2) - phaseEnergy U (trajectory g h (z.1,z.2.2) z.2.1)

theorem measurable_trajectory_count (g : E → E) (hg : Measurable g) (h : ℝ) :
    Measurable (fun z : (E × E) × ℕ => trajectory g h z.1 z.2) := by
  apply measurable_from_prod_countable_left
  intro n
  exact (trajectory_measurePreserving g hg h n).measurable

theorem measurable_verletProposal (g : E → E) (hg : Measurable g) (h : ℝ) :
    Measurable (verletProposal g h) := by
  unfold verletProposal
  exact ((measurable_trajectory_count g hg h).comp
    ((measurable_fst.prodMk measurable_snd.snd).prodMk measurable_snd.fst)).fst

theorem measurable_verletLogAcceptance (U : E → ℝ) (hU : Measurable U)
    (g : E → E) (hg : Measurable g) (h : ℝ) :
    Measurable (verletLogAcceptance U g h) := by
  have hH : Measurable (phaseEnergy U) := by
    unfold phaseEnergy
    fun_prop
  exact (hH.comp (measurable_fst.prodMk measurable_snd.snd)).sub
    (hH.comp ((measurable_trajectory_count g hg h).comp
      ((measurable_fst.prodMk measurable_snd.snd).prodMk measurable_snd.fst)))

def randomizedVerletKernel (U : E → ℝ) (hU : Measurable U)
    (g : E → E) (hg : Measurable g) (h : ℝ) (lawJ : Measure ℕ) : Kernel E E :=
  proposalKernel (verletProposal g h) (measurable_verletProposal g hg h)
    (verletLogAcceptance U g h) (measurable_verletLogAcceptance U hU g hg h)
    (lawJ.prod (stdGaussian E))

instance randomizedVerletKernel_markov (U : E → ℝ) (hU : Measurable U)
    (g : E → E) (hg : Measurable g) (h : ℝ) (lawJ : Measure ℕ)
    [IsProbabilityMeasure lawJ] : IsMarkovKernel (randomizedVerletKernel U hU g hg h lawJ) := by
  unfold randomizedVerletKernel
  infer_instance

end Verlet
end
end BreakingResonance
