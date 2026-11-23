import BreakingResonance.TransportFirstVariation
import PersistencePays.GibbsCorrector

/-! Exact changes of the transport cost and its derivative at force updates. -/
noncomputable section
namespace BreakingResonance
open PersistencePays MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def forceCorrector {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (μ : Measure (E×E)) [IsProbabilityMeasure μ] : ℝ :=
  ∫x,⟪gradient U x,x-positionBrenierMap μ a.targetProbability x⟫ ∂μ.fst

theorem corrector_zero_of_centered_velocity {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (μ : Measure (E×E)) [IsProbabilityMeasure μ] (hμ : MemLp id 2 μ)
    (hK : klDiv μ (phaseGibbs U)≠∞)
    (hc : ∀ᵐ x ∂μ.fst,conditionalMeanVelocity μ x=0) : a.corrector μ=0 := by
  rw [A1.corrector,transportCorrector_conditional μ a.targetProbability hμ
    a.position_memLp_two (a.position_absolutelyContinuous μ hK)]
  apply integral_eq_zero_of_ae
  filter_upwards [hc] with x hx
  simp [hx]

theorem force_update_corrector {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (μ : Measure (E×E)) [IsProbabilityMeasure μ] (hμ : MemLp id 2 μ)
    (hK : klDiv μ (phaseGibbs U)≠∞) (t : ℝ) :
    let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
    a.corrector (μ.map (kickEquiv (gradient U) hg t))=
      a.corrector μ-t*forceCorrector a μ := by
  dsimp only
  exact transportCorrector_kick μ a.targetProbability hμ a.position_memLp_two
    (a.position_absolutelyContinuous μ hK) (gradient U)
    (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
    (a.gradient_memLp hμ.fst) t

theorem forceCorrector_decomposition {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (μ : Measure (E×E)) [IsProbabilityMeasure μ] (hμ : MemLp id 2 μ)
    (hK : klDiv μ (phaseGibbs U)≠∞) :
    forceCorrector a μ=a.transportGap μ+
      (klDiv μ.fst (positionGibbs U)).toReal-
      (boltzmannEntropy μ.fst-boltzmannEntropy (positionGibbs U)) :=
  (a.transportGap_identity μ hμ hK).2.2

theorem forceCorrector_lower_bound {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (μ : Measure (E×E)) [IsProbabilityMeasure μ] (hμ : MemLp id 2 μ)
    (hK : klDiv μ (phaseGibbs U)≠∞) :
    (klDiv μ.fst (positionGibbs U)).toReal-
      (boltzmannEntropy μ.fst-boltzmannEntropy (positionGibbs U))≤forceCorrector a μ := by
  rw [forceCorrector_decomposition a μ hμ hK]
  linarith [(a.transportGap_identity μ hμ hK).2.1]

theorem forceCorrector_potential_identity {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (μ : Measure (E×E)) [IsProbabilityMeasure μ] (hμ : MemLp id 2 μ)
    (hK : klDiv μ (phaseGibbs U)≠∞) :
    forceCorrector a μ=a.transportGap μ+(∫x,U x ∂μ.fst)-(∫x,U x ∂positionGibbs U) := by
  letI : IsProbabilityMeasure (positionGibbs U) := a.gibbs_isProbabilityMeasure
  have hm : MemLp id 2 μ.fst :=
    (memLp_map_measure_iff measurable_id.aestronglyMeasurable measurable_fst.aemeasurable).mpr hμ.fst
  have hμb := (gibbs_boltzmann_identity U a.gibbs_integrable μ.fst
    (a.potential_integrable hm) (a.position_entropy_finite μ hK)).2
  have hπb := (gibbs_boltzmann_identity U a.gibbs_integrable (positionGibbs U)
    (a.potential_integrable a.position_memLp_two) (by simp)).2
  simp only [klDiv_self,ENNReal.toReal_zero,zero_sub] at hπb
  rw [forceCorrector_decomposition a μ hμ hK]
  linarith

theorem forceCorrector_potential_lower {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (μ : Measure (E×E)) [IsProbabilityMeasure μ] (hμ : MemLp id 2 μ)
    (hK : klDiv μ (phaseGibbs U)≠∞) :
    (∫x,U x ∂μ.fst)-(∫x,U x ∂positionGibbs U)≤forceCorrector a μ := by
  rw [forceCorrector_potential_identity a μ hμ hK]
  linarith [(a.transportGap_identity μ hμ hK).2.1]

theorem positionCost_kick (μ : Measure (E×E)) [IsProbabilityMeasure μ]
    (ξ : ProbabilityMeasure E) (g : E → E) (hg : Measurable g) (t : ℝ) :
    positionCost (μ.map (kickEquiv g hg t)) ξ=positionCost μ ξ := by
  have he := map_position_preserving_fst μ (kickEquiv g hg t) (fun _=>rfl)
  simp only [positionCost,he]

end BreakingResonance
