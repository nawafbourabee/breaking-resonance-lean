import BreakingResonance.SharpFreeTransport
import BreakingResonance.TransportFirstVariation
import BreakingResonance.WeightedCalculus
import PersistencePays.FreeTransportGibbsEntropy

/-! The free-drift estimates for the actual transported probability measures. -/
noncomputable section
namespace BreakingResonance
open PersistencePays MeasureTheory ProbabilityTheory InformationTheory Set
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def freeDriftRate (U : E → ℝ) (μ : Measure (E×E)) (t : ℝ) : ℝ :=
  2*(conditionalGaussianEntropy μ (stdGaussian E) t).toReal-
    (boltzmannEntropy (transportPosition μ t)-boltzmannEntropy (positionGibbs U))

theorem freeDriftRate_shift (U : E → ℝ) (μ : Measure (E×E)) (u t : ℝ) :
    freeDriftRate U (transportJoint μ u) t=freeDriftRate U μ (u+t) := by
  simp only [freeDriftRate,conditionalGaussianEntropy,transportPosition,
    transportJoint_transportJoint]

theorem freeDriftRate_continuous {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (μ : Measure (E×E)) [IsProbabilityMeasure μ] (hμ : MemLp id 2 μ)
    (hK : klDiv μ (phaseGibbs U)≠∞) : Continuous (freeDriftRate U μ) :=
  sharp_continuous_freeTransport_upper_rate a μ hμ hK

theorem freeDriftRate_entropy_identity {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (μ : Measure (E×E)) [IsProbabilityMeasure μ] (hμ : MemLp id 2 μ)
    (hK : klDiv μ (phaseGibbs U)≠∞) (t : ℝ) :
    freeDriftRate U μ t=
      2*(klDiv (transportJoint μ t) (phaseGibbs U)).toReal-
      3*(klDiv (transportPosition μ t) (positionGibbs U)).toReal+
      (∫z,U z.1 ∂transportJoint μ t)-(∫x,U x ∂positionGibbs U) := by
  letI : IsProbabilityMeasure (positionGibbs U) := a.gibbs_isProbabilityMeasure
  have hm := transportProbability_memLp μ hμ t
  have hk := a.freeTransport_gibbs_entropy_finite μ hμ hK t
  have hj := a.phase_entropy_eq_sum (transportJoint μ t) hk
  have hp := (a.position_boltzmann_identity (transportJoint μ t) hm hk).2
  have ht := (gibbs_boltzmann_identity U a.gibbs_integrable (positionGibbs U)
    (a.potential_integrable a.position_memLp_two) (by simp)).2
  have he : conditionalGaussianEntropy (transportJoint μ t) (stdGaussian E) 0=
      conditionalGaussianEntropy μ (stdGaussian E) t := by
    simp only [conditionalGaussianEntropy,transportJoint_zero,transportPosition_zero]
    rfl
  rw [he] at hj
  change (klDiv (transportJoint μ t) (phaseGibbs U)).toReal=
    (klDiv (transportPosition μ t) (positionGibbs U)).toReal+
      (conditionalGaussianEntropy μ (stdGaussian E) t).toReal at hj
  simp only [show (transportJoint μ t).fst=transportPosition μ t from rfl] at hp
  simp only [klDiv_self,ENNReal.toReal_zero,zero_sub] at ht
  dsimp [freeDriftRate]
  linarith

theorem freeDrift_corrector_increment {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (μ : Measure (E×E)) [IsProbabilityMeasure μ] (hμ : MemLp id 2 μ)
    (hK : klDiv μ (phaseGibbs U)≠∞) {u v : ℝ} (huv : u≤v) :
    a.corrector (transportJoint μ v)-a.corrector (transportJoint μ u)≤
      ∫t in u..v,freeDriftRate U μ t := by
  rcases eq_or_lt_of_le huv with he|he
  · subst v
    simp
  have hm := transportProbability_memLp μ hμ u
  change MemLp id 2 (transportJoint μ u) at hm
  have hk := a.freeTransport_gibbs_entropy_finite μ hμ hK u
  have hh := sharp_free_transport_corrector a
    (⟨transportJoint μ u,inferInstance⟩ : ProbabilityMeasure (E×E)) hm hk (sub_pos.mpr he)
  change a.corrector (transportJoint (transportJoint μ u) (v-u))-
    a.corrector (transportJoint μ u)≤
      sharpFreeTransportRHS (transportJoint μ u) (positionGibbs U) (v-u) at hh
  rw [←sharpFreeTransportRHS_integral_identity a (transportJoint μ u) hm hk (sub_pos.mpr he)] at hh
  change a.corrector (transportJoint (transportJoint μ u) (v-u))-
    a.corrector (transportJoint μ u)≤
      ∫t in (0:ℝ)..v-u,freeDriftRate U (transportJoint μ u) t at hh
  simp only [transportJoint_transportJoint,show u+(v-u)=v by ring] at hh
  simp_rw [freeDriftRate_shift] at hh
  rw [intervalIntegral.integral_comp_add_left] at hh
  simpa only [add_zero,show u+(v-u)=v by ring] using hh

theorem freeDrift_weighted_cost_bound {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (μ : Measure (E×E)) [IsProbabilityMeasure μ] (hμ : MemLp id 2 μ)
    (hK : klDiv μ (phaseGibbs U)≠∞) {u v : ℝ} (huv : u≤v) :
    positionCost (transportJoint μ v) a.targetProbability-
      positionCost (transportJoint μ u) a.targetProbability≤
      (v-u)*a.corrector (transportJoint μ u)+
        ∫t in u..v,(v-t)*freeDriftRate U μ t := by
  have hac : μ≪(volume : Measure E).prod volume := by
    apply (klDiv_ne_top_iff.mp hK).1.trans
    rw [phaseGibbs_eq_tilted U a.twice_contDiff.continuous.measurable a.gibbs_integrable]
    exact tilted_absolutelyContinuous _ _
  apply weighted_increment_bound huv
    (continuous_freeTransport_corrector μ a.targetProbability hμ a.position_memLp_two hac)
    (freeDriftRate_continuous a μ hμ hK)
  · intro t _
    exact freeTransport_positionCost_hasDerivAt μ a.targetProbability hμ
      a.position_memLp_two hac t
  · intro t ht
    exact freeDrift_corrector_increment a μ hμ hK ht.1

end BreakingResonance
