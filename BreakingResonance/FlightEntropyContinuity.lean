import BreakingResonance.FreeDrift

/-! Continuity of the actual position and joint Gibbs entropies along free flight. -/
noncomputable section
namespace BreakingResonance
open PersistencePays MeasureTheory ProbabilityTheory InformationTheory Filter
open scoped ENNReal Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem freeFlight_potential_integral {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (μ : Measure (E×E)) (t : ℝ) :
    (∫z,U z.1 ∂transportJoint μ t)=(∫z,U (z.1+t • z.2) ∂μ) :=
  integral_map (measurable_freeTransport t).aemeasurable
    (show AEStronglyMeasurable (fun z : E×E=>U z.1) (transportJoint μ t) from
      (a.twice_contDiff.continuous.measurable.comp measurable_fst).aestronglyMeasurable)

theorem potential_abs_bound {U : E → ℝ} {m L : ℝ} (a : A1 U m L) (x : E) :
    |U x|≤L/2*‖x-a.minimizer‖^2+|U a.minimizer| := by
  have hu := a.potential_upper_at_minimizer x
  have hl := a.minimizer_le x
  have hn := mul_nonneg (show 0≤L/2 by linarith [a.L_pos]) (sq_nonneg ‖x-a.minimizer‖)
  exact abs_le.mpr ⟨by linarith [neg_abs_le (U a.minimizer)],
    by linarith [le_abs_self (U a.minimizer)]⟩

theorem continuous_freeFlight_potential {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (μ : Measure (E×E)) [IsProbabilityMeasure μ] (hμ : MemLp id 2 μ) :
    Continuous (fun t : ℝ=>∫z,U (z.1+t • z.2) ∂μ) := by
  apply continuous_iff_continuousAt.mpr
  intro t₀
  let B := |t₀|+1
  let f : E×E → ℝ := fun z=>‖z.1-a.minimizer‖+B*‖z.2‖
  have hf : MemLp f 2 μ :=
    ((hμ.fst.sub (memLp_const a.minimizer)).norm).add (hμ.snd.norm.const_mul B)
  have hi : Integrable (fun z=>L/2*(f z)^2+|U a.minimizer|) μ :=
    (hf.integrable_sq.const_mul (L/2)).add (integrable_const _)
  apply continuousAt_of_dominated (bound:=fun z=>L/2*(f z)^2+|U a.minimizer|)
  · exact .of_forall (fun t=>
      (a.twice_contDiff.continuous.measurable.comp
        (measurable_fst.add (measurable_const.smul measurable_snd))).aestronglyMeasurable)
  · filter_upwards [Metric.ball_mem_nhds t₀ zero_lt_one] with t ht
    apply Filter.Eventually.of_forall
    intro z
    have ht' : |t-t₀|<1 := by simpa only [Metric.mem_ball,Real.dist_eq] using ht
    have htB : |t|≤B := by
      have he : t=(t-t₀)+t₀ := by ring
      calc
        |t|=|(t-t₀)+t₀| := congrArg abs he
        _≤|t-t₀|+|t₀| := abs_add_le _ _
        _≤B := by dsimp [B]; linarith
    have hd : ‖z.1+t • z.2-a.minimizer‖≤f z := by
      calc
        _=‖(z.1-a.minimizer)+t • z.2‖ := by congr 1; module
        _≤‖z.1-a.minimizer‖+‖t • z.2‖ := norm_add_le _ _
        _≤f z := by
          rw [norm_smul,Real.norm_eq_abs]
          exact add_le_add le_rfl (mul_le_mul_of_nonneg_right htB (norm_nonneg z.2))
    have hb := potential_abs_bound a (z.1+t • z.2)
    have hs : ‖z.1+t • z.2-a.minimizer‖^2≤(f z)^2 :=
      pow_le_pow_left₀ (norm_nonneg _) hd 2
    rw [Real.norm_eq_abs]
    exact hb.trans (add_le_add
      (mul_le_mul_of_nonneg_left hs (show 0≤L/2 by linarith [a.L_pos])) le_rfl)
  · exact hi
  · exact .of_forall (fun z=>
      (a.twice_contDiff.continuous.comp (continuous_const.add
        (continuous_id.smul continuous_const))).continuousAt)

theorem continuous_freeFlight_position_entropy {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (μ : Measure (E×E)) [IsProbabilityMeasure μ] (hμ : MemLp id 2 μ)
    (hK : klDiv μ (phaseGibbs U)≠∞) :
    Continuous (fun t : ℝ=>(klDiv (transportPosition μ t) (positionGibbs U)).toReal) := by
  have hG := a.phaseGaussian_entropy_finite μ hμ hK
  have he (t : ℝ) : (klDiv (transportPosition μ t) (positionGibbs U)).toReal=
      boltzmannEntropy (transportPosition μ t)+(∫z,U (z.1+t • z.2) ∂μ)+
        Real.log (∫x,Real.exp (-U x)) := by
    have hb := (a.position_boltzmann_identity (transportJoint μ t)
      (transportProbability_memLp μ hμ t) (a.freeTransport_gibbs_entropy_finite μ hμ hK t)).2
    have hi : (∫z,U z.1 ∂transportJoint μ t)=∫z,U (z.1+t • z.2) ∂μ := by
      exact integral_map (measurable_freeTransport t).aemeasurable
        (show AEStronglyMeasurable (fun z : E×E=>U z.1) (transportJoint μ t) from
          (a.twice_contDiff.continuous.measurable.comp measurable_fst).aestronglyMeasurable)
    rw [hi] at hb
    simp only [show (transportJoint μ t).fst=transportPosition μ t from rfl] at hb
    linarith
  simp_rw [he]
  exact ((continuous_freeTransport_boltzmann μ hμ hG).add
    (continuous_freeFlight_potential a μ hμ)).add continuous_const

theorem continuous_freeFlight_joint_entropy {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (μ : Measure (E×E)) [IsProbabilityMeasure μ] (hμ : MemLp id 2 μ)
    (hK : klDiv μ (phaseGibbs U)≠∞) :
    Continuous (fun t : ℝ=>(klDiv (transportJoint μ t) (phaseGibbs U)).toReal) := by
  have he (t : ℝ) : (klDiv (transportJoint μ t) (phaseGibbs U)).toReal=
      (klDiv (transportPosition μ t) (positionGibbs U)).toReal+
        (conditionalGaussianEntropy μ (stdGaussian E) t).toReal := by
    have hb := a.phase_entropy_eq_sum (transportJoint μ t)
      (a.freeTransport_gibbs_entropy_finite μ hμ hK t)
    simpa only [conditionalGaussianEntropy,transportJoint_zero,transportPosition_zero,
      show (transportJoint μ t).fst=transportPosition μ t from rfl] using hb
  simp_rw [he]
  exact (continuous_freeFlight_position_entropy a μ hμ hK).add
    (continuous_freeTransport_conditional_entropy μ hμ (a.phaseGaussian_entropy_finite μ hμ hK))

end BreakingResonance
