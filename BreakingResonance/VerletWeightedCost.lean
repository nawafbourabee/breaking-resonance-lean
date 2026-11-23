import BreakingResonance.CellLaws
import BreakingResonance.FreeDrift
import BreakingResonance.WeightedDiscrete

/-! Summation of the actual free-flight estimates and force-update identities. -/
noncomputable section
namespace BreakingResonance
open PersistencePays MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem verlet_weighted_transport_bound {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (μ : ProbabilityMeasure (E×E)) (hμ : MemLp id 2 (μ : Measure (E×E)))
    (hK : klDiv (μ : Measure (E×E)) (phaseGibbs U)≠∞)
    {h : ℝ} (hh : 0≤h) (N : ℕ) :
    let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
    let ν := fun n σ=>(flightLaw (gradient U) hg μ h n σ : Measure (E×E))
    let Q := fun n σ=>freeDriftRate U (ν n 0) σ
    positionCost (ν N 0) a.targetProbability-positionCost (ν 0 0) a.targetProbability≤
      (N:ℝ)*h*a.corrector (ν 0 0)+
      ∑n∈Finset.range N,((∫σ in (0:ℝ)..h,(h-σ)*Q n σ)+
        ((N:ℝ)-(n+1))*h*((∫σ in (0:ℝ)..h,Q n σ)-h*forceCorrector a (ν n h))) := by
  dsimp only
  let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
  let ν := fun n σ=>(flightLaw (gradient U) hg μ h n σ : Measure (E×E))
  let Q := fun n σ=>freeDriftRate U (ν n 0) σ
  have hm (n : ℕ) (σ : ℝ) : MemLp id 2 (ν n σ) := flightLaw_memLp a μ hμ h n σ
  have hk (n : ℕ) (σ : ℝ) : klDiv (ν n σ) (phaseGibbs U)≠∞ :=
    flightLaw_entropy_finite a μ hμ hK h n σ
  have hshift (n : ℕ) (σ : ℝ) : ν n σ=transportJoint (ν n 0) σ :=
    flightLaw_freeTransport _ hg μ h n σ
  have hsucc (n : ℕ) : ν (n+1) 0=(ν n h).map (kickEquiv (gradient U) hg h) :=
    flightLaw_successor _ hg μ h n
  have hW (n : ℕ) : positionCost (ν (n+1) 0) a.targetProbability-
      positionCost (ν n 0) a.targetProbability≤
      h*a.corrector (ν n 0)+(∫σ in (0:ℝ)..h,(h-σ)*Q n σ) := by
    have hb := freeDrift_weighted_cost_bound a (ν n 0) (hm n 0) (hk n 0) hh
    simp only [transportJoint_zero,sub_zero] at hb
    have hp : positionCost (ν (n+1) 0) a.targetProbability=
        positionCost (ν n h) a.targetProbability := by
      simp only [hsucc,positionCost_kick]
    rw [hp]
    simpa only [hshift n h] using hb
  have hC (n : ℕ) : a.corrector (ν (n+1) 0)-a.corrector (ν n 0)≤
      (∫σ in (0:ℝ)..h,Q n σ)-h*forceCorrector a (ν n h) := by
    have hb := freeDrift_corrector_increment a (ν n 0) (hm n 0) (hk n 0) hh
    simp only [transportJoint_zero] at hb
    have hc : a.corrector (ν (n+1) 0)=a.corrector (ν n h)-h*forceCorrector a (ν n h) := by
      simpa only [hsucc] using force_update_corrector a (ν n h) (hm n h) (hk n h) h
    rw [hc]
    have he : a.corrector (ν n h)=a.corrector (transportJoint (ν n 0) h) := by
      simp only [hshift n h]
    rw [he]
    linarith
  exact weighted_discrete_accumulation N hh
    (fun n=>positionCost (ν n 0) a.targetProbability) (fun n=>a.corrector (ν n 0))
    (fun n=>∫σ in (0:ℝ)..h,(h-σ)*Q n σ)
    (fun n=>(∫σ in (0:ℝ)..h,Q n σ)-h*forceCorrector a (ν n h))
    (fun n _=>hW n) (fun n _=>hC n)

end BreakingResonance
