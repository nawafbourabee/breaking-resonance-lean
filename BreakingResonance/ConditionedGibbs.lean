import BreakingResonance.ForceCorrector
import PersistencePays.TruncationApproximation
import PersistencePays.GibbsTail

/-! Entropy and centering of the stationary law conditioned on a position set
and an energy sublevel set. -/
noncomputable section
namespace BreakingResonance
open PersistencePays MeasureTheory ProbabilityTheory InformationTheory Set
open scoped ENNReal RealInnerProductSpace

theorem cond_map_invariant {S : Type*} [MeasurableSpace S]
    (μ : Measure S) (f : S → S) (hf : Measurable f)
    (hμ : μ.map f=μ) (A : Set S) (hA : MeasurableSet A) (hpre : f ⁻¹' A=A) :
    (cond μ A).map f=cond μ A := by
  have hr := Measure.restrict_map (μ:=μ) hf hA
  rw [hμ,hpre] at hr
  rw [ProbabilityTheory.cond,Measure.map_smul,←hr]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def energyEvent (U : E → ℝ) (A : Set E) (R : ℝ) : Set (E×E) :=
  {z | z.1∈A ∧ phaseEnergy U z≤R}

theorem energyEvent_measurable (U : E → ℝ) (hU : Measurable U)
    (A : Set E) (hA : MeasurableSet A) (R : ℝ) : MeasurableSet (energyEvent U A R) :=
  (hA.preimage measurable_fst).inter
    (measurableSet_le (phaseEnergy_measurable U hU) measurable_const)

theorem phaseGibbs_flip_invariant (U : E → ℝ) :
    (phaseGibbs U).map (velocityFlip : E×E → E×E)=phaseGibbs U := by
  have hn : MeasurePreserving (fun v : E=>-v) (stdGaussian E) (stdGaussian E) :=
    ⟨measurable_neg,stdGaussian_map (LinearIsometryEquiv.neg ℝ)⟩
  exact ((MeasurePreserving.id (positionGibbs U)).prod hn).map_eq

theorem conditionedGibbs_flip_invariant (U : E → ℝ) (hU : Measurable U)
    (A : Set E) (hA : MeasurableSet A) (R : ℝ) :
    (cond (phaseGibbs U) (energyEvent U A R)).map (velocityFlip : E×E → E×E)=
      cond (phaseGibbs U) (energyEvent U A R) := by
  apply cond_map_invariant _ _ (by unfold velocityFlip; fun_prop)
    (phaseGibbs_flip_invariant U) _ (energyEvent_measurable U hU A hA R)
  ext z
  simp [energyEvent,velocityFlip,phaseEnergy_eq_norm]

theorem corrector_zero_of_flip_invariant {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (μ : Measure (E×E)) [IsProbabilityMeasure μ]
    (hf : μ.map (velocityFlip : E×E → E×E)=μ) : a.corrector μ=0 := by
  have hm : Measurable (fun z : E×E=>⟪z.2,z.1-positionBrenierMap μ a.targetProbability z.1⟫) :=
    measurable_snd.inner (measurable_fst.sub
      ((measurable_positionBrenierMap μ a.targetProbability).comp measurable_fst))
  have he := integral_map (μ:=μ) (show AEMeasurable (velocityFlip : E×E → E×E) μ from
    (by unfold velocityFlip; fun_prop)) hm.aestronglyMeasurable
  rw [hf] at he
  change (∫z,⟪z.2,z.1-positionBrenierMap μ a.targetProbability z.1⟫ ∂μ)=
    ∫z,⟪-z.2,z.1-positionBrenierMap μ a.targetProbability z.1⟫ ∂μ at he
  simp only [inner_neg_left,integral_neg] at he
  change (∫z,⟪z.2,z.1-positionBrenierMap μ a.targetProbability z.1⟫ ∂μ)=0
  linarith

theorem conditionedGibbs_entropy {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (A : Set E) (hA : MeasurableSet A) (R : ℝ)
    (hp : phaseGibbs U (energyEvent U A R)≠0) :
    klDiv (cond (phaseGibbs U) (energyEvent U A R)) (phaseGibbs U)≠∞ ∧
    (klDiv (cond (phaseGibbs U) (energyEvent U A R)) (phaseGibbs U)).toReal=
      -Real.log ((phaseGibbs U (energyEvent U A R)).toReal) := by
  letI : IsProbabilityMeasure (positionGibbs U) := a.gibbs_isProbabilityMeasure
  letI : IsProbabilityMeasure (phaseGibbs U) := by unfold phaseGibbs; infer_instance
  exact conditional_klDiv_self _ _
    (energyEvent_measurable U a.twice_contDiff.continuous.measurable A hA R) hp

theorem conditionedGibbs_corrector_zero {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (A : Set E) (hA : MeasurableSet A) (R : ℝ)
    (hp : phaseGibbs U (energyEvent U A R)≠0) :
    letI : IsProbabilityMeasure (positionGibbs U) := a.gibbs_isProbabilityMeasure
    letI : IsProbabilityMeasure (phaseGibbs U) := by unfold phaseGibbs; infer_instance
    letI : IsProbabilityMeasure (cond (phaseGibbs U) (energyEvent U A R)) := cond_isProbabilityMeasure hp
    a.corrector (cond (phaseGibbs U) (energyEvent U A R))=0 := by
  letI : IsProbabilityMeasure (positionGibbs U) := a.gibbs_isProbabilityMeasure
  letI : IsProbabilityMeasure (phaseGibbs U) := by unfold phaseGibbs; infer_instance
  letI : IsProbabilityMeasure (cond (phaseGibbs U) (energyEvent U A R)) := cond_isProbabilityMeasure hp
  exact corrector_zero_of_flip_invariant a _
    (conditionedGibbs_flip_invariant U a.twice_contDiff.continuous.measurable A hA R)

end BreakingResonance
