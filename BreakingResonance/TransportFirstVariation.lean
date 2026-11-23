import PersistencePays.FreeTransportCorrectorContinuity
import PersistencePays.FlowTransportCost
import BreakingResonance.ScalarFirstVariation

/-! First variation of the actual quadratic transport cost along a free flight. -/
noncomputable section
namespace BreakingResonance
open PersistencePays MeasureTheory ProbabilityTheory Filter Set QuadraticTransport
open scoped ENNReal Topology RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def positionCost (μ : Measure (E×E)) [IsProbabilityMeasure μ]
    (ξ : ProbabilityMeasure E) : ℝ :=
  (cost (⟨μ.fst,inferInstance⟩ : ProbabilityMeasure E) ξ).toReal/2

theorem freeTransport_cost_expansion (μ : Measure (E×E)) [IsProbabilityMeasure μ]
    (ξ : ProbabilityMeasure E) (hμ : MemLp id 2 μ) (hξ : MemLp id 2 (ξ : Measure E))
    (hac : μ.fst ≪ volume) (t : ℝ) :
    positionCost (transportJoint μ t) ξ ≤ positionCost μ ξ+
      t*transportCorrector μ ξ+(t^2/2)*(∫z,‖z.2‖^2 ∂μ) := by
  let ν : ProbabilityMeasure E := ⟨μ.fst,inferInstance⟩
  let νt : ProbabilityMeasure E := ⟨transportPosition μ t,inferInstance⟩
  let T := positionBrenierMap μ ξ
  have hν : MemLp id 2 (ν : Measure E) :=
    (memLp_map_measure_iff measurable_id.aestronglyMeasurable measurable_fst.aemeasurable).mpr hμ.fst
  have hs := brenierMap_spec ν ξ hν hξ hac
  have hTm : Measurable T := measurable_positionBrenierMap μ ξ
  have hT2 : MemLp (fun z:E×E=>T z.1) 2 μ :=
    (memLp_map_measure_iff hTm.aestronglyMeasurable measurable_fst.aemeasurable).mp
      (brenierMap_memLp ν ξ hν hξ hac)
  have hd : MemLp (fun z:E×E=>z.1-T z.1) 2 μ := hμ.fst.sub hT2
  have hνt : MemLp id 2 (νt : Measure E) :=
    (memLp_map_measure_iff measurable_id.aestronglyMeasurable measurable_fst.aemeasurable).mpr
      (transportProbability_memLp μ hμ t).fst
  let F : E×E → E×E := fun z=>(z.1+t • z.2,T z.1)
  have hF : Measurable F :=
    (measurable_fst.add (measurable_const.smul measurable_snd)).prodMk
      (hTm.comp measurable_fst)
  let η : ProbabilityMeasure (E×E) := ⟨μ.map F,Measure.isProbabilityMeasure_map hF.aemeasurable⟩
  have hη : η ∈ plans νt ξ := by
    constructor
    · apply Subtype.ext
      change (μ.map F).map Prod.fst=(transportJoint μ t).map Prod.fst
      rw [Measure.map_map measurable_fst hF]
      rw [transportJoint,Measure.map_map measurable_fst (measurable_freeTransport t)]
      rfl
    · apply Subtype.ext
      change (μ.map F).map Prod.snd=(ξ:Measure E)
      rw [Measure.map_map measurable_snd hF]
      change μ.map (T ∘ Prod.fst)=(ξ:Measure E)
      rw [←Measure.map_map hTm measurable_fst]
      exact hs.2.1
  have hb := ENNReal.toReal_mono
    (squaredCost_finite νt ξ η hη hνt.integrable_norm_pow' hξ.integrable_norm_pow')
    (show cost νt ξ≤ squaredCost η from iInf₂_le η hη)
  rw [squaredCost_toReal νt ξ η hη hνt hξ] at hb
  have he : (∫z,‖z.1-z.2‖^2 ∂(η:Measure (E×E)))=
      ∫z,‖(z.1-T z.1)+t • z.2‖^2 ∂μ := by
    change (∫z,‖z.1-z.2‖^2 ∂μ.map F)=_
    rw [integral_map hF.aemeasurable (by fun_prop)]
    congr 1
    funext z
    congr 2
    dsimp [F]
    abel
  rw [he] at hb
  have heq (z:E×E) : ‖(z.1-T z.1)+t • z.2‖^2=
      ‖z.1-T z.1‖^2+2*t*⟪z.2,z.1-T z.1⟫+t^2*‖z.2‖^2 := by
    rw [norm_add_sq_real,inner_smul_right,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,
      real_inner_comm (z.1-T z.1) z.2]
    ring
  simp_rw [heq] at hb
  have hd2 := hd.integrable_norm_pow'
  have hv2 := hμ.snd.integrable_norm_pow'
  have hinner := integrable_inner_of_memLp_two hμ.snd hd
  simp only [id_eq] at hv2 hinner
  rw [integral_add (f:=fun z:E×E=>‖z.1-T z.1‖^2+2*t*⟪z.2,z.1-T z.1⟫)
      (g:=fun z:E×E=>t^2*‖z.2‖^2)
      (hd2.add (hinner.const_mul (2*t))) (hv2.const_mul (t^2)),
    integral_add hd2 (hinner.const_mul (2*t)),integral_const_mul,integral_const_mul] at hb
  have hcost : (∫z,‖z.1-T z.1‖^2 ∂μ)=(cost ν ξ).toReal := by
    calc
      _ = ∫x,‖x-T x‖^2 ∂μ.fst :=
        (integral_map measurable_fst.aemeasurable
          ((measurable_id.sub hTm).norm.pow_const 2).aestronglyMeasurable).symm
      _ = _ := brenierMap_displacement_cost ν ξ hν hξ hac
  rw [hcost] at hb
  change (cost νt ξ).toReal/2≤(cost ν ξ).toReal/2+
    t*(∫z,⟪z.2,z.1-T z.1⟫ ∂μ)+(t^2/2)*(∫z,‖z.2‖^2 ∂μ)
  linarith

theorem transportJoint_transportJoint (μ : Measure (E×E)) (s t : ℝ) :
    transportJoint (transportJoint μ s) t=transportJoint μ (s+t) := by
  simp only [transportJoint]
  rw [Measure.map_map (measurable_freeTransport t) (measurable_freeTransport s)]
  congr 1
  funext z
  ext <;> simp [Function.comp_def,freeTransport,drift,add_smul] <;> module

theorem transportJoint_velocity_second_moment (μ : Measure (E×E)) (t : ℝ) :
    (∫z,‖z.2‖^2 ∂transportJoint μ t)=(∫z,‖z.2‖^2 ∂μ) := by
  rw [transportJoint,integral_map (measurable_freeTransport t).aemeasurable (by fun_prop)]
  rfl

/-- The derivative is the actual Brenier corrector. No smooth density or
regularity of the Brenier map is assumed. -/
theorem freeTransport_positionCost_hasDerivAt (μ : Measure (E×E)) [IsProbabilityMeasure μ]
    (ξ : ProbabilityMeasure E) (hμ : MemLp id 2 μ) (hξ : MemLp id 2 (ξ : Measure E))
    (hac : μ ≪ (volume : Measure E).prod volume) (t : ℝ) :
    HasDerivAt (fun s=>positionCost (transportJoint μ s) ξ)
      (transportCorrector (transportJoint μ t) ξ) t := by
  apply hasDerivAt_of_quadratic_upper_bounds
    (M:=∫z,‖z.2‖^2 ∂μ) (integral_nonneg (fun z=>sq_nonneg _))
    (continuous_freeTransport_corrector μ ξ hμ hξ hac)
  intro x y
  have hax : (transportJoint μ x).fst≪volume := by
    change transportPosition μ x≪volume
    rw [transportPosition_eq_withDensity μ hac x]
    exact withDensity_absolutelyContinuous _ _
  have hh := freeTransport_cost_expansion (transportJoint μ x) ξ
    (transportProbability_memLp μ hμ x) hξ hax (y-x)
  simp only [transportJoint_transportJoint,show x+(y-x)=y by ring,
    transportJoint_velocity_second_moment] at hh
  nlinarith

end BreakingResonance
