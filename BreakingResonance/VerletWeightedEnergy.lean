import BreakingResonance.VerletNodeEntropy
import BreakingResonance.VerletPotentialQuadrature

/-! The signed energy cancellation in the weighted joint relative entropy. -/
noncomputable section
namespace BreakingResonance
open PersistencePays MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem flight_endpoint_potential {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (μ : ProbabilityMeasure (E×E)) (h : ℝ) (n : ℕ) :
    let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
    (∫z,U z.1 ∂(flightLaw (gradient U) hg μ h n h : Measure (E×E)))=
      (∫z,U z.1 ∂(trajectoryLaw (gradient U) hg μ h (n+1) : Measure (E×E))) := by
  dsimp only
  rw [←potential_integral_fst a,flightLaw_endpoint_position,flightLaw_initial_position,
    potential_integral_fst a]

theorem verlet_weighted_joint_entropy {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (μ : ProbabilityMeasure (E×E)) (hμ : MemLp id 2 (μ : Measure (E×E)))
    (hK : klDiv (μ : Measure (E×E)) (phaseGibbs U)≠∞) (h : ℝ) (N : ℕ) :
    let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
    let ζ := fun n=>(trajectoryLaw (gradient U) hg μ h n : Measure (E×E))
    let ν := fun n σ=>(flightLaw (gradient U) hg μ h n σ : Measure (E×E))
    let e := fun n=>(klDiv (ζ n) (phaseGibbs U)).toReal+
      (∫z,modifiedEnergy U (gradient U) h z-phaseEnergy U z ∂ζ n)
    let Q := fun n=>∫z,cellRemainder U (gradient U) h h z ∂ζ n
    let u := fun n=>∫z,U z.1 ∂ζ n
    (∑n∈Finset.range N,∫σ in (0:ℝ)..h,(((N:ℝ)-n)*h-σ)*
      (klDiv (ν n σ) (phaseGibbs U)).toReal)=
      (∑n∈Finset.range N,triangularWeight h N n*e n)-h^2/12*(u N-u 0)+
      h^2/12*(∑n∈Finset.range N,Q n)+
      (∑n∈Finset.range N,∫σ in (0:ℝ)..h,(((N:ℝ)-n)*h-σ)*
        (∫z,cellRemainder U (gradient U) h σ z ∂ζ n)) := by
  dsimp only
  let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
  let ζ := fun n=>(trajectoryLaw (gradient U) hg μ h n : Measure (E×E))
  let ν := fun n σ=>(flightLaw (gradient U) hg μ h n σ : Measure (E×E))
  let e := fun n=>(klDiv (ζ n) (phaseGibbs U)).toReal+
    (∫z,modifiedEnergy U (gradient U) h z-phaseEnergy U z ∂ζ n)
  let Q := fun n=>∫z,cellRemainder U (gradient U) h h z ∂ζ n
  let u := fun n=>∫z,U z.1 ∂ζ n
  let F := fun n=>∫z,⟪gradient U z.1,flightVelocity (gradient U) h z⟫ ∂ζ n
  have hincr (n : ℕ) : u (n+1)-u n=h*F n+Q n := by
    have hi := cell_potential_increment a (ζ n) (trajectoryLaw_memLp a μ hμ h n) h
    change (∫z,U z.1 ∂ν n h)-u n=h*F n+Q n at hi
    rw [flight_endpoint_potential a] at hi
    exact hi
  have he (n : ℕ) :
      (∫σ in (0:ℝ)..h,(((N:ℝ)-n)*h-σ)*(klDiv (ν n σ) (phaseGibbs U)).toReal)=
        triangularWeight h N n*e n-h^2/12*(u (n+1)-u n)+h^2/12*Q n+
        (∫σ in (0:ℝ)..h,(((N:ℝ)-n)*h-σ)*(∫z,cellRemainder U (gradient U) h σ z ∂ζ n)) := by
    have hw := cell_weighted_entropy_identity a (ζ n) (trajectoryLaw_memLp a μ hμ h n)
      (trajectoryLaw_entropy_finite a μ hμ hK h n) (((N:ℝ)-n)*h) h
    change (∫σ in (0:ℝ)..h,(((N:ℝ)-n)*h-σ)*(klDiv (ν n σ) (phaseGibbs U)).toReal)=
      triangularWeight h N n*e n-h^3/12*F n+_ at hw
    rw [hw,hincr]
    ring
  change (∑n∈Finset.range N,∫σ in (0:ℝ)..h,(((N:ℝ)-n)*h-σ)*
    (klDiv (ν n σ) (phaseGibbs U)).toReal)=_
  simp_rw [he]
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib,Finset.sum_sub_distrib,
    ←Finset.mul_sum,←Finset.mul_sum,sum_consecutive_differences]

end BreakingResonance
