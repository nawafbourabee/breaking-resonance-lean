import BreakingResonance.FlightEntropyContinuity

/-! The entropy decomposition inside the weighted free-flight integral. -/
noncomputable section
namespace BreakingResonance
open PersistencePays MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem weighted_entropy_rate {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (μ : Measure (E×E)) [IsProbabilityMeasure μ] (hμ : MemLp id 2 μ)
    (hK : klDiv μ (phaseGibbs U)≠∞) (A h : ℝ) :
    (∫σ in (0:ℝ)..h,(A-σ)*freeDriftRate U μ σ)=
      2*(∫σ in (0:ℝ)..h,(A-σ)*(klDiv (transportJoint μ σ) (phaseGibbs U)).toReal)-
      3*(∫σ in (0:ℝ)..h,(A-σ)*(klDiv (transportPosition μ σ) (positionGibbs U)).toReal)+
      (∫σ in (0:ℝ)..h,(A-σ)*((∫z,U (z.1+σ • z.2) ∂μ)-(∫x,U x ∂positionGibbs U))) := by
  let J := fun σ=>(klDiv (transportJoint μ σ) (phaseGibbs U)).toReal
  let X := fun σ=>(klDiv (transportPosition μ σ) (positionGibbs U)).toReal
  let V := fun (σ : ℝ)=>(∫z,U (z.1+σ • z.2) ∂μ)-(∫x,U x ∂positionGibbs U)
  have hJ : Continuous J := continuous_freeFlight_joint_entropy a μ hμ hK
  have hX : Continuous X := continuous_freeFlight_position_entropy a μ hμ hK
  have hV : Continuous V := (continuous_freeFlight_potential a μ hμ).sub continuous_const
  have he (σ : ℝ) : (A-σ)*freeDriftRate U μ σ=
      2*((A-σ)*J σ)-3*((A-σ)*X σ)+(A-σ)*V σ := by
    rw [freeDriftRate_entropy_identity a μ hμ hK,freeFlight_potential_integral a]
    dsimp [J,X,V]
    ring
  simp_rw [he]
  rw [intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul]

end BreakingResonance
