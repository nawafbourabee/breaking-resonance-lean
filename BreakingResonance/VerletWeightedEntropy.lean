import BreakingResonance.VerletWeightedEnergy

/-! The weighted entropy inequality for the actual numerical trajectory.
The common cell entropy is kept as a single expression until the energy bound is applied. -/
noncomputable section
namespace BreakingResonance
open PersistencePays MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem verlet_weighted_entropy_of_interpolation (hPP : PPInterpolation E) {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (μ : ProbabilityMeasure (E×E)) (hμ : MemLp id 2 (μ : Measure (E×E)))
    (hK : klDiv (μ : Measure (E×E)) (phaseGibbs U)≠∞)
    (hc : a.corrector (μ : Measure (E×E))=0)
    {h : ℝ} (hh : 0<h) (N : ℕ) :
    let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
    let ζ := fun n=>(trajectoryLaw (gradient U) hg μ h n : Measure (E×E))
    let ν := fun n σ=>(flightLaw (gradient U) hg μ h n σ : Measure (E×E))
    let e := fun n=>(klDiv (ζ n) (phaseGibbs U)).toReal+
      (∫z,modifiedEnergy U (gradient U) h z-phaseEnergy U z ∂ζ n)
    let Q := fun n=>∫z,cellRemainder U (gradient U) h h z ∂ζ n
    let u := fun n=>∫z,U z.1 ∂ζ n
    3*(∑n∈Finset.range N,triangularWeight h N n*
      ((klDiv (ν n 0).fst (positionGibbs U)).toReal+
        (klDiv (ν n h).fst (positionGibbs U)).toReal))≤
      positionCost (μ : Measure (E×E)) a.targetProbability+
      5*(∑n∈Finset.range N,triangularWeight h N n*e n)+
      3*(∑n∈Finset.range N,triangularWeight h N n*Q n)+
      h^2/4*(u N-u 0)-h^2/12*(∑n∈Finset.range N,Q n)-
      (∑n∈Finset.range N,∫σ in (0:ℝ)..h,(((N:ℝ)-n)*h-σ)*
        (∫z,cellRemainder U (gradient U) h σ z ∂ζ n)) := by
  dsimp only
  let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
  let ν := fun n σ=>(flightLaw (gradient U) hg μ h n σ : Measure (E×E))
  have hx (n : ℕ) (σ : ℝ) : transportPosition (ν n 0) σ=(ν n σ).fst :=
    congrArg Measure.fst (flightLaw_freeTransport (gradient U) hg μ h n σ).symm
  have hj (n : ℕ) (σ : ℝ) : transportJoint (ν n 0) σ=ν n σ :=
    (flightLaw_freeTransport (gradient U) hg μ h n σ).symm
  have hv := verlet_integrated_entropy_centered a μ hμ hK hc hh N
  have hn := verlet_node_transfer_of_interpolation hPP a μ hμ hK hh N
  have he := verlet_endpoint_entropy_sum a μ hμ hK h N
  have hw := verlet_weighted_joint_entropy a μ hμ hK h N
  dsimp only at hv hn he hw
  dsimp only [ν] at hx hj
  simp_rw [hx, hj, flightLaw_initial_position, potential_integral_fst a] at hv
  linarith only [hv, hn, he, hw]

theorem verlet_weighted_entropy {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (μ : ProbabilityMeasure (E×E)) (hμ : MemLp id 2 (μ : Measure (E×E)))
    (hK : klDiv (μ : Measure (E×E)) (phaseGibbs U)≠∞)
    (hc : a.corrector (μ : Measure (E×E))=0)
    {h : ℝ} (hh : 0<h) (N : ℕ) :
    let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
    let ζ := fun n=>(trajectoryLaw (gradient U) hg μ h n : Measure (E×E))
    let ν := fun n σ=>(flightLaw (gradient U) hg μ h n σ : Measure (E×E))
    let e := fun n=>(klDiv (ζ n) (phaseGibbs U)).toReal+
      (∫z,modifiedEnergy U (gradient U) h z-phaseEnergy U z ∂ζ n)
    let Q := fun n=>∫z,cellRemainder U (gradient U) h h z ∂ζ n
    let u := fun n=>∫z,U z.1 ∂ζ n
    3*(∑n∈Finset.range N,triangularWeight h N n*
      ((klDiv (ν n 0).fst (positionGibbs U)).toReal+
        (klDiv (ν n h).fst (positionGibbs U)).toReal))≤
      positionCost (μ : Measure (E×E)) a.targetProbability+
      5*(∑n∈Finset.range N,triangularWeight h N n*e n)+
      3*(∑n∈Finset.range N,triangularWeight h N n*Q n)+
      h^2/4*(u N-u 0)-h^2/12*(∑n∈Finset.range N,Q n)-
      (∑n∈Finset.range N,∫σ in (0:ℝ)..h,(((N:ℝ)-n)*h-σ)*
        (∫z,cellRemainder U (gradient U) h σ z ∂ζ n)) :=
  verlet_weighted_entropy_of_interpolation
    (fun μ _ hh _ _ hσ => freeTransport_interval (μ : Measure (E × E)) hh hσ.1 hσ.2)
    a μ hμ hK hc hh N

/-- The weighted inequality with the initial relative entropy (E_0) and the
modified energy differences written separately, as in Lemma 6.7. -/
theorem verlet_weighted_entropy_with_initial_entropy (hPP : PPInterpolation E)
    {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (μ : ProbabilityMeasure (E × E)) (hμ : MemLp id 2 (μ : Measure (E × E)))
    (hK : klDiv (μ : Measure (E × E)) (phaseGibbs U) ≠ ∞)
    (hc : ∀ᵐ x ∂(μ : Measure (E × E)).fst,
      conditionalMeanVelocity (μ : Measure (E × E)) x = 0)
    {h : ℝ} (hh : 0 < h) (N : ℕ) :
    let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
    let ζ := fun n => (trajectoryLaw (gradient U) hg μ h n : Measure (E × E))
    let E₀ := (klDiv (μ : Measure (E × E)) (phaseGibbs U)).toReal
    let Epos := fun n => (klDiv (ζ n).fst (positionGibbs U)).toReal
    let b := fun n => (∫ z, modifiedEnergy U (gradient U) h z ∂ζ n) -
      (∫ z, phaseEnergy U z ∂(μ : Measure (E × E)))
    let Q := fun n => ∫ z, cellRemainder U (gradient U) h h z ∂ζ n
    let u := fun n => ∫ z, U z.1 ∂ζ n
    3 * (∑ n ∈ Finset.range N, triangularWeight h N n * (Epos n + Epos (n + 1))) ≤
      positionCost (μ : Measure (E × E)) a.targetProbability +
      5/2 * E₀ * ((N : ℝ) * h)^2 +
      5 * (∑ n ∈ Finset.range N, triangularWeight h N n * b n) +
      3 * (∑ n ∈ Finset.range N, triangularWeight h N n * Q n) +
      h^2/4 * (u N - u 0) - h^2/12 * (∑ n ∈ Finset.range N, Q n) -
      (∑ n ∈ Finset.range N, ∫ σ in (0 : ℝ)..h, (((N : ℝ) - n) * h - σ) *
        (∫ z, cellRemainder U (gradient U) h σ z ∂ζ n)) := by
  dsimp only
  let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
  let ζ := fun n => (trajectoryLaw (gradient U) hg μ h n : Measure (E × E))
  let E₀ := (klDiv (μ : Measure (E × E)) (phaseGibbs U)).toReal
  let b := fun n => (∫ z, modifiedEnergy U (gradient U) h z ∂ζ n) -
    (∫ z, phaseEnergy U z ∂(μ : Measure (E × E)))
  have he (n : ℕ) : (klDiv (ζ n) (phaseGibbs U)).toReal +
      (∫ z, modifiedEnergy U (gradient U) h z - phaseEnergy U z ∂ζ n) =
      E₀ + b n := by
    have hm := trajectoryLaw_memLp a μ hμ h n
    have hs := modifiedEnergy_difference_integrable a (ζ n) hm h
    have hp : Integrable (phaseEnergy U) (ζ n) := a.phaseEnergy_integrable hm
    have hi : Integrable (modifiedEnergy U (gradient U) h) (ζ n) := by
      have hsum : (fun z => modifiedEnergy U (gradient U) h z - phaseEnergy U z +
          phaseEnergy U z) = modifiedEnergy U (gradient U) h := by
        funext z
        ring
      have hint := hs.add hp
      change Integrable (fun z => modifiedEnergy U (gradient U) h z - phaseEnergy U z +
        phaseEnergy U z) (ζ n) at hint
      rwa [hsum] at hint
    rw [integral_sub hi hp]
    have ht := (trajectory_entropy_change a (μ : Measure (E × E)) hμ hK h n).2
    have hinit : Integrable (phaseEnergy U) (μ : Measure (E × E)) :=
      a.phaseEnergy_integrable hμ
    have hstep : Integrable (fun z => phaseEnergy U (trajectory (gradient U) h z n))
        (μ : Measure (E × E)) := a.phaseEnergy_integrable (trajectory_memLp a hμ h n)
    rw [integral_sub hstep hinit] at ht
    have hmap :
        (∫ z, phaseEnergy U (trajectory (gradient U) h z n) ∂(μ : Measure (E × E))) =
        ∫ z, phaseEnergy U z ∂ζ n := by
      exact (integral_map (trajectory_measurePreserving (gradient U) hg h n).measurable.aemeasurable
        hp.aestronglyMeasurable).symm
    rw [hmap] at ht
    change (klDiv (ζ n) (phaseGibbs U)).toReal = E₀ + _ at ht
    rw [ht]
    dsimp only [b]
    ring
  have hw := verlet_weighted_entropy_of_interpolation hPP a μ hμ hK
    (corrector_zero_of_centered_velocity a (μ : Measure (E × E)) hμ hK hc) hh N
  dsimp only at hw
  have hsum : (∑ n ∈ Finset.range N, triangularWeight h N n * (E₀ + b n)) =
      (((N : ℝ) * h)^2 / 2) * E₀ +
      ∑ n ∈ Finset.range N, triangularWeight h N n * b n := by
    simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, triangularWeight_sum]
  dsimp only [ζ] at he
  dsimp only [E₀, b, ζ] at hsum
  simp_rw [flightLaw_endpoint_position, flightLaw_initial_position, he] at hw
  rw [hsum] at hw
  linarith only [hw]

end BreakingResonance
