import BreakingResonance.VerletWeightedCost
import BreakingResonance.WeightedEntropyRate
import BreakingResonance.VerletQuadrature

/-! Integrated free-flight inequality for the actual Verlet trajectory. -/
noncomputable section
namespace BreakingResonance
open PersistencePays MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem verlet_integrated_flight {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (μ : ProbabilityMeasure (E×E)) (hμ : MemLp id 2 (μ : Measure (E×E)))
    (hK : klDiv (μ : Measure (E×E)) (phaseGibbs U)≠∞)
    {h : ℝ} (hh : 0≤h) (N : ℕ) :
    let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
    let ν := fun n σ=>(flightLaw (gradient U) hg μ h n σ : Measure (E×E))
    let weight := fun (n : ℕ) σ=>((N:ℝ)-n)*h-σ
    let J := fun n=>∫σ in (0:ℝ)..h,weight n σ*
      (klDiv (transportJoint (ν n 0) σ) (phaseGibbs U)).toReal
    let X := fun n=>∫σ in (0:ℝ)..h,weight n σ*
      (klDiv (transportPosition (ν n 0) σ) (positionGibbs U)).toReal
    let V := fun n=>∫σ in (0:ℝ)..h,weight n σ*
      ((∫z,U (z.1+σ • z.2) ∂ν n 0)-(∫x,U x ∂positionGibbs U))
    positionCost (ν N 0) a.targetProbability+3*(∑n∈Finset.range N,X n)≤
      positionCost (ν 0 0) a.targetProbability+(N:ℝ)*h*a.corrector (ν 0 0)+
      2*(∑n∈Finset.range N,J n)+(∑n∈Finset.range N,V n)-
      h*(∑n∈Finset.range N,((N:ℝ)-(n+1))*h*forceCorrector a (ν n h)) := by
  dsimp only
  let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
  let ν := fun n σ=>(flightLaw (gradient U) hg μ h n σ : Measure (E×E))
  let weight := fun (n : ℕ) σ=>((N:ℝ)-n)*h-σ
  let c := fun (n : ℕ)=>((N:ℝ)-(n+1))*h
  let Q := fun n σ=>freeDriftRate U (ν n 0) σ
  let J := fun n=>∫σ in (0:ℝ)..h,weight n σ*
    (klDiv (transportJoint (ν n 0) σ) (phaseGibbs U)).toReal
  let X := fun n=>∫σ in (0:ℝ)..h,weight n σ*
    (klDiv (transportPosition (ν n 0) σ) (positionGibbs U)).toReal
  let V := fun n=>∫σ in (0:ℝ)..h,weight n σ*
    ((∫z,U (z.1+σ • z.2) ∂ν n 0)-(∫x,U x ∂positionGibbs U))
  have hm (n : ℕ) : MemLp id 2 (ν n 0) := flightLaw_memLp a μ hμ h n 0
  have hk (n : ℕ) : klDiv (ν n 0) (phaseGibbs U)≠∞ := flightLaw_entropy_finite a μ hμ hK h n 0
  have he (n : ℕ) : (∫σ in (0:ℝ)..h,(h-σ)*Q n σ)+
      c n*((∫σ in (0:ℝ)..h,Q n σ)-h*forceCorrector a (ν n h))=
      2*J n-3*X n+V n-h*(c n*forceCorrector a (ν n h)) := by
    have hw : h+c n=((N:ℝ)-n)*h := by dsimp [c]; ring
    calc
      _=((∫σ in (0:ℝ)..h,(h-σ)*Q n σ)+c n*(∫σ in (0:ℝ)..h,Q n σ))-
        h*(c n*forceCorrector a (ν n h)) := by ring
      _=(∫σ in (0:ℝ)..h,weight n σ*Q n σ)-h*(c n*forceCorrector a (ν n h)) := by
        rw [combine_weighted_integrals h (c n) (Q n) (freeDriftRate_continuous a (ν n 0) (hm n) (hk n)),hw]
      _=_ := by
        have hr := weighted_entropy_rate a (ν n 0) (hm n) (hk n) (((N:ℝ)-n)*h) h
        change (∫σ in (0:ℝ)..h,weight n σ*Q n σ)=2*J n-3*X n+V n at hr
        rw [hr]
  have hb := verlet_weighted_transport_bound a μ hμ hK hh N
  change positionCost (ν N 0) a.targetProbability-positionCost (ν 0 0) a.targetProbability≤
    (N:ℝ)*h*a.corrector (ν 0 0)+
      ∑n∈Finset.range N,((∫σ in (0:ℝ)..h,(h-σ)*Q n σ)+
        c n*((∫σ in (0:ℝ)..h,Q n σ)-h*forceCorrector a (ν n h))) at hb
  simp_rw [he] at hb
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,←Finset.mul_sum] at hb
  change positionCost (ν N 0) a.targetProbability+3*(∑n∈Finset.range N,X n)≤
    positionCost (ν 0 0) a.targetProbability+(N:ℝ)*h*a.corrector (ν 0 0)+
    2*(∑n∈Finset.range N,J n)+(∑n∈Finset.range N,V n)-
    h*(∑n∈Finset.range N,c n*forceCorrector a (ν n h))
  linarith

end BreakingResonance
