import BreakingResonance.FlightEntropyContinuity
import BreakingResonance.FreeTransport
import BreakingResonance.VerletQuadrature

/-! Transfer of the interpolated entropy estimate to the two numerical endpoints. -/
noncomputable section
namespace BreakingResonance
open PersistencePays MeasureTheory ProbabilityTheory InformationTheory Set
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem freeFlight_velocity_entropy_identity {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (μ : Measure (E×E)) [IsProbabilityMeasure μ] (hμ : MemLp id 2 μ)
    (hK : klDiv μ (phaseGibbs U)≠∞) (t : ℝ) :
    (conditionalGaussianEntropy μ (stdGaussian E) t).toReal=
      (klDiv (transportJoint μ t) (phaseGibbs U)).toReal-
      (klDiv (transportPosition μ t) (positionGibbs U)).toReal := by
  have he := a.phase_entropy_eq_sum (transportJoint μ t)
    (a.freeTransport_gibbs_entropy_finite μ hμ hK t)
  have hc : conditionalGaussianEntropy (transportJoint μ t) (stdGaussian E) 0=
      conditionalGaussianEntropy μ (stdGaussian E) t := by
    simp only [conditionalGaussianEntropy,transportJoint_zero,transportPosition_zero]
    rfl
  rw [hc] at he
  simp only [show (transportJoint μ t).fst=transportPosition μ t from rfl] at he
  linarith

/-- Lemma 6.4, the interpolation inequality of Persistence Pays for finite
endpoint entropies on a free flight of duration h. Its conclusion also implies
finiteness of the intermediate entropies. -/
def PPInterpolation (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] : Prop :=
  ∀ (μ : ProbabilityMeasure (E × E)) (h : ℝ), 0 < h →
    let e := conditionalGaussianEntropy (μ : Measure (E × E)) (stdGaussian E)
    e 0 + e h ≠ ∞ → ∀ σ ∈ Icc 0 h, e σ ≤ e 0 + e h

theorem freeFlight_endpoint_entropy_bound_of_interpolation (hPP : PPInterpolation E)
{U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (μ : Measure (E×E)) [IsProbabilityMeasure μ] (hμ : MemLp id 2 μ)
    (hK : klDiv μ (phaseGibbs U)≠∞) {h σ : ℝ} (hh : 0<h) (hσ : σ∈Icc 0 h) :
    let J := fun t=>(klDiv (transportJoint μ t) (phaseGibbs U)).toReal
    let X := fun t=>(klDiv (transportPosition μ t) (positionGibbs U)).toReal
    X 0+X h≤X σ-J σ+J 0+J h := by
  dsimp only
  have hfinite := ENNReal.add_ne_top.mpr ⟨(a.free_transport_entropy_balance μ hμ hK 0).1,
      (a.free_transport_entropy_balance μ hμ hK h).1⟩
  have he := ENNReal.toReal_mono hfinite (hPP ⟨μ, inferInstance⟩ h hh hfinite σ hσ)
  change (conditionalGaussianEntropy μ (stdGaussian E) σ).toReal ≤
    (conditionalGaussianEntropy μ (stdGaussian E) 0 +
      conditionalGaussianEntropy μ (stdGaussian E) h).toReal at he
  rw [ENNReal.toReal_add (a.free_transport_entropy_balance μ hμ hK 0).1
    (a.free_transport_entropy_balance μ hμ hK h).1] at he
  simp_rw [freeFlight_velocity_entropy_identity a μ hμ hK] at he
  linarith

theorem freeFlight_node_transfer_of_interpolation (hPP : PPInterpolation E) {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (μ : Measure (E×E)) [IsProbabilityMeasure μ] (hμ : MemLp id 2 μ)
    (hK : klDiv μ (phaseGibbs U)≠∞) {A h : ℝ} (hh : 0<h) (hA : h≤A) :
    let J := fun t=>(klDiv (transportJoint μ t) (phaseGibbs U)).toReal
    let X := fun t=>(klDiv (transportPosition μ t) (positionGibbs U)).toReal
    (h*A-h^2/2)*(X 0+X h)≤
      (∫σ in (0:ℝ)..h,(A-σ)*X σ)-(∫σ in (0:ℝ)..h,(A-σ)*J σ)+
      (h*A-h^2/2)*(J 0+J h) := by
  dsimp only
  let J := fun t=>(klDiv (transportJoint μ t) (phaseGibbs U)).toReal
  let X := fun t=>(klDiv (transportPosition μ t) (positionGibbs U)).toReal
  have hJ : Continuous J := continuous_freeFlight_joint_entropy a μ hμ hK
  have hX : Continuous X := continuous_freeFlight_position_entropy a μ hμ hK
  have hbound : ∀σ∈Icc 0 h,(A-σ)*(X 0+X h)≤
      (A-σ)*X σ-(A-σ)*J σ+(A-σ)*(J 0+J h) := by
    intro σ hσ
    have he := mul_le_mul_of_nonneg_left
      (freeFlight_endpoint_entropy_bound_of_interpolation hPP a μ hμ hK hh hσ)
      (sub_nonneg.mpr (hσ.2.trans hA))
    dsimp only at he
    dsimp [X,J]
    nlinarith
  have hb := intervalIntegral.integral_mono_on (μ:=volume) hh.le
    (show IntervalIntegrable (fun σ=>(A-σ)*(X 0+X h)) volume 0 h from
      (by apply Continuous.intervalIntegrable; fun_prop))
    (show IntervalIntegrable (fun σ=>(A-σ)*X σ-(A-σ)*J σ+(A-σ)*(J 0+J h)) volume 0 h from
      (by apply Continuous.intervalIntegrable; fun_prop)) hbound
  rw [intervalIntegral.integral_mul_const,linear_weight_integral,
    intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_mul_const,linear_weight_integral] at hb
  exact hb

theorem freeFlight_endpoint_entropy_bound {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (μ : Measure (E×E)) [IsProbabilityMeasure μ] (hμ : MemLp id 2 μ)
    (hK : klDiv μ (phaseGibbs U)≠∞) {h σ : ℝ} (hh : 0<h) (hσ : σ∈Icc 0 h) :
    let J := fun t=>(klDiv (transportJoint μ t) (phaseGibbs U)).toReal
    let X := fun t=>(klDiv (transportPosition μ t) (positionGibbs U)).toReal
    X 0+X h≤X σ-J σ+J 0+J h :=
  freeFlight_endpoint_entropy_bound_of_interpolation
    (fun μ _ hh _ _ hσ => freeTransport_interval (μ : Measure (E × E)) hh hσ.1 hσ.2)
    a μ hμ hK hh hσ

theorem freeFlight_node_transfer {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (μ : Measure (E×E)) [IsProbabilityMeasure μ] (hμ : MemLp id 2 μ)
    (hK : klDiv μ (phaseGibbs U)≠∞) {A h : ℝ} (hh : 0<h) (hA : h≤A) :
    let J := fun t=>(klDiv (transportJoint μ t) (phaseGibbs U)).toReal
    let X := fun t=>(klDiv (transportPosition μ t) (positionGibbs U)).toReal
    (h*A-h^2/2)*(X 0+X h)≤
      (∫σ in (0:ℝ)..h,(A-σ)*X σ)-(∫σ in (0:ℝ)..h,(A-σ)*J σ)+
      (h*A-h^2/2)*(J 0+J h) :=
  freeFlight_node_transfer_of_interpolation
    (fun μ _ hh _ _ hσ => freeTransport_interval (μ : Measure (E × E)) hh hσ.1 hσ.2)
    a μ hμ hK hh hA

end BreakingResonance
