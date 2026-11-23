import BreakingResonance.RestrictedLevelSets

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace BreakingResonance

variable {S V : Type*} [MeasurableSpace S] [MeasurableSpace V]

/-- The Metropolis decision for a measurable acceptance probability. -/
def conditionalMetropolisDecision (Q : S×V → S) (hQ : Measurable Q)
    (α : S×V → ℝ≥0∞) (hα : Measurable α) : Kernel (S×V) S where
  toFun z := α z • Measure.dirac (Q z)+(1-α z) • Measure.dirac z.1
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro A hA
    simp only [Measure.add_apply,Measure.smul_apply,smul_eq_mul]
    exact (hα.mul ((Kernel.deterministic Q hQ).measurable_coe hA)).add
      ((measurable_const.sub hα).mul
        ((Kernel.deterministic Prod.fst measurable_fst).measurable_coe hA))

theorem conditionalMetropolisDecision_markov (Q : S×V → S) (hQ : Measurable Q)
    (α : S×V → ℝ≥0∞) (hα : Measurable α) (hα₁ : ∀ z, α z ≤ 1) :
    IsMarkovKernel (conditionalMetropolisDecision Q hQ α hα) where
  isProbabilityMeasure z := by
    constructor
    change (α z • Measure.dirac (Q z)+(1-α z) • Measure.dirac z.1) univ = 1
    simp only [Measure.add_apply,Measure.smul_apply,Measure.dirac_apply_of_mem (mem_univ _),
      smul_eq_mul,mul_one,add_tsub_cancel_of_le (hα₁ z)]

/-- A proposal with general conditional refreshment followed by a Metropolis decision. -/
def conditionalMetropolisKernel (Q : S×V → S) (hQ : Measurable Q)
    (α : S×V → ℝ≥0∞) (hα : Measurable α) (refresh : Kernel S V) : Kernel S S :=
  conditionalMetropolisDecision Q hQ α hα ∘ₖ (Kernel.id ×ₖ refresh)

theorem conditionalMetropolisKernel_markov (Q : S×V → S) (hQ : Measurable Q)
    (α : S×V → ℝ≥0∞) (hα : Measurable α) (hα₁ : ∀ z, α z ≤ 1)
    (refresh : Kernel S V) [IsMarkovKernel refresh] :
    IsMarkovKernel (conditionalMetropolisKernel Q hQ α hα refresh) := by
  let : IsMarkovKernel (conditionalMetropolisDecision Q hQ α hα) :=
    conditionalMetropolisDecision_markov Q hQ α hα hα₁
  unfold conditionalMetropolisKernel
  infer_instance

theorem conditionalMetropolisKernel_apply (Q : S×V → S) (hQ : Measurable Q)
    (α : S×V → ℝ≥0∞) (hα : Measurable α) (refresh : Kernel S V) [IsMarkovKernel refresh]
    (x : S) (A : Set S) (hA : MeasurableSet A) :
    conditionalMetropolisKernel Q hQ α hα refresh x A =
      ∫⁻ v, α (x,v)*A.indicator (fun _ => 1) (Q (x,v)) +
        (1-α (x,v))*A.indicator (fun _ => 1) x ∂refresh x := by
  rw [conditionalMetropolisKernel,Kernel.comp_apply' _ _ _ hA,
    Kernel.lintegral_id_prod ((conditionalMetropolisDecision Q hQ α hα).measurable_coe hA)]
  apply lintegral_congr
  intro v
  simp [conditionalMetropolisDecision,Measure.dirac_apply' _ hA,smul_eq_mul]
  rfl

theorem conditionalMetropolisKernel_exit_flow
    (π : Measure S) [IsProbabilityMeasure π]
    (Q : S×V → S) (hQ : Measurable Q) (α : S×V → ℝ≥0∞) (hα : Measurable α)
    (hα₁ : ∀ z, α z ≤ 1) (refresh : Kernel S V) [IsMarkovKernel refresh]
    (A : Set S) (hA : MeasurableSet A) :
    (π ⊗ₘ conditionalMetropolisKernel Q hQ α hα refresh) (A ×ˢ Aᶜ) =
      ∫⁻ z, A.indicator (fun _ => 1) z.1 *
        (α z*Aᶜ.indicator (fun _ => 1) (Q z)) ∂(π ⊗ₘ refresh) := by
  haveI := conditionalMetropolisKernel_markov Q hQ α hα hα₁ refresh
  rw [Measure.compProd_apply_prod hA hA.compl,← lintegral_indicator hA]
  have hm : Measurable (fun z : S×V => A.indicator (fun _ => (1:ℝ≥0∞)) z.1 *
      (α z*Aᶜ.indicator (fun _ => 1) (Q z))) :=
    ((measurable_const.indicator hA).comp measurable_fst).mul
      (hα.mul ((measurable_const.indicator hA.compl).comp hQ))
  rw [Measure.lintegral_compProd hm]
  apply lintegral_congr
  intro x
  by_cases hx : x ∈ A
  · rw [indicator_of_mem hx,conditionalMetropolisKernel_apply Q hQ α hα refresh x Aᶜ hA.compl]
    simp [hx]
  · simp [hx]

end BreakingResonance

#print axioms BreakingResonance.conditionalMetropolisKernel_apply
#print axioms BreakingResonance.conditionalMetropolisKernel_exit_flow
