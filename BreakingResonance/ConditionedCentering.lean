import BreakingResonance.ConditionedGibbs
import PersistencePays.CorrectorConditional
import Mathlib.Probability.Kernel.Disintegration.Unique

noncomputable section

open MeasureTheory ProbabilityTheory Set PersistencePays
open scoped ProbabilityTheory

namespace BreakingResonance

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Momentum-flip symmetry of the joint law implies zero conditional
mean of momentum. -/
theorem conditionalMeanVelocity_zero_of_flip_invariant (μ : Measure (E×E))
    [IsProbabilityMeasure μ] (hflip : μ.map (velocityFlip : E×E → E×E) = μ) :
    ∀ᵐ x ∂μ.fst, conditionalMeanVelocity μ x = 0 := by
  let f := fun v : E => -v
  let F := velocityFlip (E := E)
  have hm : Measurable f := measurable_neg
  have hFm : Measurable F := measurable_fst.prodMk (measurable_neg.comp measurable_snd)
  let κ := μ.condKernel
  have hd : μ.fst ⊗ₘ κ = μ := μ.disintegrate κ
  have he : μ.fst ⊗ₘ κ.map f = μ := by
    apply Measure.ext_prod
    intro A B hA hB
    have hp : F ⁻¹' (A×ˢ B) = A×ˢ (f ⁻¹' B) := rfl
    have hh : (μ.map F) (A×ˢ B) = μ (A×ˢ B) := congrArg (fun ν : Measure (E×E) => ν (A×ˢ B)) hflip
    rw [Measure.map_apply hFm (hA.prod hB),hp,← hd,
      Measure.compProd_apply_prod hA (hB.preimage hm)] at hh
    calc
      _ = ∫⁻ x in A, κ.map f x B ∂μ.fst := Measure.compProd_apply_prod hA hB
      _ = ∫⁻ x in A, κ x (f ⁻¹' B) ∂μ.fst := by
        apply lintegral_congr
        intro x
        rw [Kernel.map_apply' _ hm _ hB]
      _ = _ := by rwa [hd] at hh
  have hk := eq_condKernel_of_measure_eq_compProd (κ.map f) he.symm
  filter_upwards [hk] with x hx
  have hm' : (κ x).map f = κ x := by
    rw [Kernel.map_apply _ hm] at hx
    exact hx
  have hi := integral_map hm.aemeasurable
    (stronglyMeasurable_id.aestronglyMeasurable (μ := (κ x).map f))
  rw [hm'] at hi
  change (∫ v, v ∂κ x) = ∫ v, -v ∂κ x at hi
  rw [integral_neg] at hi
  change (∫ v, v ∂κ x) = 0
  have hsum : (2 : ℝ) • (∫ v, v ∂κ x) = 0 := by
    rw [two_smul]
    exact eq_neg_iff_add_eq_zero.mp hi
  exact (smul_eq_zero.mp hsum).resolve_left (by norm_num)

/-- The energy-conditioned Gibbs law satisfies the centering hypothesis
of the Verlet proposal-entropy estimate. -/
theorem conditionedGibbs_centered (U : E → ℝ) (hU : Measurable U)
    (hZ : Integrable (fun x => Real.exp (-U x)) volume)
    (A : Set E) (hA : MeasurableSet A) (R : ℝ)
    (hE : phaseGibbs U (energyEvent U A R) ≠ 0) :
    letI : IsProbabilityMeasure (cond (phaseGibbs U) (energyEvent U A R)) :=
      cond_isProbabilityMeasure hE
    ∀ᵐ x ∂(cond (phaseGibbs U) (energyEvent U A R)).fst,
      conditionalMeanVelocity (cond (phaseGibbs U) (energyEvent U A R)) x = 0 := by
  let : IsProbabilityMeasure (positionGibbs U) := isProbabilityMeasure_tilted hZ
  let : IsProbabilityMeasure (phaseGibbs U) := by unfold phaseGibbs; infer_instance
  let : IsProbabilityMeasure (cond (phaseGibbs U) (energyEvent U A R)) :=
    cond_isProbabilityMeasure hE
  exact conditionalMeanVelocity_zero_of_flip_invariant _
    (conditionedGibbs_flip_invariant U hU A hA R)

end BreakingResonance

#print axioms BreakingResonance.conditionedGibbs_centered
