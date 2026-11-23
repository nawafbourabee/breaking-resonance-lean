import BreakingResonance.VerletIntegratedFlight
import BreakingResonance.ConvexFlight

/-! Summation of the convexity bounds in the weighted Verlet calculation. -/
noncomputable section
namespace BreakingResonance
open PersistencePays MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem potential_integral_fst {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (μ : Measure (E×E)) : (∫x,U x ∂μ.fst)=(∫z,U z.1 ∂μ) :=
  integral_map measurable_fst.aemeasurable a.twice_contDiff.continuous.aestronglyMeasurable

theorem verlet_potential_quadrature {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (μ : ProbabilityMeasure (E×E)) (hμ : MemLp id 2 (μ : Measure (E×E)))
    {h : ℝ} (hh : 0<h) (N : ℕ) :
    let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
    let ν := fun n σ=>(flightLaw (gradient U) hg μ h n σ : Measure (E×E))
    let u := fun n=>(∫x,U x ∂(ν n 0).fst)-(∫x,U x ∂positionGibbs U)
    (∑n∈Finset.range N,∫σ in (0:ℝ)..h,(((N:ℝ)-n)*h-σ)*
      ((∫z,U (z.1+σ • z.2) ∂ν n 0)-(∫x,U x ∂positionGibbs U)))≤
      h*((N:ℝ)*h/2*u 0+(∑n∈Finset.range N,((N:ℝ)-(n+1))*h*u (n+1)))+
      h^2/6*(u N-u 0) := by
  dsimp only
  let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
  let ν := fun n σ=>(flightLaw (gradient U) hg μ h n σ : Measure (E×E))
  let u := fun n=>(∫x,U x ∂(ν n 0).fst)-(∫x,U x ∂positionGibbs U)
  have he (n : ℕ) : (∫z,U (z.1+h • z.2) ∂ν n 0)=∫x,U x ∂(ν (n+1) 0).fst := by
    rw [←freeFlight_potential_integral a,←potential_integral_fst a]
    change (∫x,U x ∂(transportJoint (ν n 0) h).fst)=_
    rw [←flightLaw_freeTransport,flightLaw_endpoint_position]
  have hb := Finset.sum_le_sum (s:=Finset.range N) (fun n hn=>
    flight_weighted_potential_chord a (ν n 0) (flightLaw_memLp a μ hμ h n 0) hh
      (show h≤((N:ℝ)-n)*h by
        have hc : (n:ℝ)+1≤N := by exact_mod_cast Finset.mem_range.mp hn
        nlinarith) (∫x,U x ∂positionGibbs U))
  simp_rw [he,←potential_integral_fst a] at hb
  change (∑n∈Finset.range N,∫σ in (0:ℝ)..h,(((N:ℝ)-n)*h-σ)*
      ((∫z,U (z.1+σ • z.2) ∂ν n 0)-(∫x,U x ∂positionGibbs U)))≤
    ∑n∈Finset.range N,((h*(((N:ℝ)-n)*h)/2-h^2/6)*u n+
      (h*(((N:ℝ)-n)*h)/2-h^2/3)*u (n+1)) at hb
  rw [weighted_endpoint_quadrature] at hb
  exact hb

theorem verlet_integrated_entropy_centered {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (μ : ProbabilityMeasure (E×E)) (hμ : MemLp id 2 (μ : Measure (E×E)))
    (hK : klDiv (μ : Measure (E×E)) (phaseGibbs U)≠∞)
    (hc : a.corrector (μ : Measure (E×E))=0)
    {h : ℝ} (hh : 0<h) (N : ℕ) :
    let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
    let ν := fun n σ=>(flightLaw (gradient U) hg μ h n σ : Measure (E×E))
    let u := fun n=>(∫x,U x ∂(ν n 0).fst)-(∫x,U x ∂positionGibbs U)
    let J := fun n=>∫σ in (0:ℝ)..h,(((N:ℝ)-n)*h-σ)*
      (klDiv (transportJoint (ν n 0) σ) (phaseGibbs U)).toReal
    let X := fun n=>∫σ in (0:ℝ)..h,(((N:ℝ)-n)*h-σ)*
      (klDiv (transportPosition (ν n 0) σ) (positionGibbs U)).toReal
    3*(∑n∈Finset.range N,X n)≤positionCost (μ : Measure (E×E)) a.targetProbability+
      2*(∑n∈Finset.range N,J n)+h^2/6*(u N-u 0) := by
  dsimp only
  let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
  let ν := fun n σ=>(flightLaw (gradient U) hg μ h n σ : Measure (E×E))
  let u := fun n=>(∫x,U x ∂(ν n 0).fst)-(∫x,U x ∂positionGibbs U)
  let c := fun n : ℕ=>((N:ℝ)-(n+1))*h
  have hm (n : ℕ) (σ : ℝ) : MemLp id 2 (ν n σ) := flightLaw_memLp a μ hμ h n σ
  have hk (n : ℕ) (σ : ℝ) : klDiv (ν n σ) (phaseGibbs U)≠∞ :=
    flightLaw_entropy_finite a μ hμ hK h n σ
  have hu0 : u 0=(∫x,U x ∂(μ : Measure (E×E)).fst)-(∫x,U x ∂positionGibbs U) := by
    dsimp [u,ν]
    rw [flightLaw_initial_position,trajectoryLaw_zero]
  have hC : a.corrector (ν 0 0)≤-(h/2)*u 0 := by
    have he := force_update_corrector a (μ : Measure (E×E)) hμ hK (h/2)
    have hν := flightLaw_initial (gradient U) hg μ h
    simp only [←hν] at he
    change a.corrector (ν 0 0)=a.corrector (μ : Measure (E×E))-(h/2)*forceCorrector a (μ : Measure (E×E)) at he
    rw [he,hc]
    have hb := mul_le_mul_of_nonneg_left (forceCorrector_potential_lower a _ hμ hK)
      (by positivity : 0≤h/2)
    rw [hu0]
    linarith
  have hC' := mul_le_mul_of_nonneg_left hC (mul_nonneg (Nat.cast_nonneg N) hh.le)
  have hforce : (∑n∈Finset.range N,c n*u (n+1))≤
      ∑n∈Finset.range N,c n*forceCorrector a (ν n h) := by
    apply Finset.sum_le_sum
    intro n hn
    have hn' : (n:ℝ)+1≤N := by exact_mod_cast Finset.mem_range.mp hn
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by linarith) hh.le)
    have hf := forceCorrector_potential_lower a (ν n h) (hm n h) (hk n h)
    change (∫x,U x ∂(flightLaw (gradient U) hg μ h n h : Measure (E×E)).fst)-_≤_ at hf
    rw [flightLaw_endpoint_position] at hf
    exact hf
  have hforce' := mul_le_mul_of_nonneg_left hforce hh.le
  have hV := verlet_potential_quadrature a μ hμ hh N
  have hb := verlet_integrated_flight a μ hμ hK hh.le N
  dsimp only at hV hb
  have hW : 0≤positionCost (ν N 0) a.targetProbability := by
    unfold positionCost
    positivity
  have hW0 : positionCost (ν 0 0) a.targetProbability=
      positionCost (μ : Measure (E×E)) a.targetProbability := by
    simp only [positionCost,ν,flightLaw_initial_position,trajectoryLaw_zero]
  rw [hW0] at hb
  dsimp only [c,u,ν] at hforce' hC' hW
  nlinarith

end BreakingResonance
