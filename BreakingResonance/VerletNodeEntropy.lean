import BreakingResonance.CellEntropy
import BreakingResonance.NodeEntropyTransfer

/-! The endpoint transfer and cancellation summed over the actual Verlet trajectory. -/
noncomputable section
namespace BreakingResonance
open PersistencePays MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem verlet_node_transfer_of_interpolation (hPP : PPInterpolation E) {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (μ : ProbabilityMeasure (E×E)) (hμ : MemLp id 2 (μ : Measure (E×E)))
    (hK : klDiv (μ : Measure (E×E)) (phaseGibbs U)≠∞)
    {h : ℝ} (hh : 0<h) (N : ℕ) :
    let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
    let ν := fun n σ=>(flightLaw (gradient U) hg μ h n σ : Measure (E×E))
    let J := fun n σ=>(klDiv (ν n σ) (phaseGibbs U)).toReal
    let X := fun n σ=>(klDiv (ν n σ).fst (positionGibbs U)).toReal
    (∑n∈Finset.range N,triangularWeight h N n*(X n 0+X n h))≤
      (∑n∈Finset.range N,∫σ in (0:ℝ)..h,(((N:ℝ)-n)*h-σ)*X n σ)-
      (∑n∈Finset.range N,∫σ in (0:ℝ)..h,(((N:ℝ)-n)*h-σ)*J n σ)+
      (∑n∈Finset.range N,triangularWeight h N n*(J n 0+J n h)) := by
  dsimp only
  let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
  let ν := fun n σ=>(flightLaw (gradient U) hg μ h n σ : Measure (E×E))
  have hx (n : ℕ) (σ : ℝ) : transportPosition (ν n 0) σ=(ν n σ).fst :=
    congrArg Measure.fst (flightLaw_freeTransport (gradient U) hg μ h n σ).symm
  have hj (n : ℕ) (σ : ℝ) : transportJoint (ν n 0) σ=ν n σ :=
    (flightLaw_freeTransport (gradient U) hg μ h n σ).symm
  have hb := Finset.sum_le_sum (s:=Finset.range N) (fun n hn=>
    freeFlight_node_transfer_of_interpolation hPP a (ν n 0) (flightLaw_memLp a μ hμ h n 0)
      (flightLaw_entropy_finite a μ hμ hK h n 0) hh
      (show h≤((N:ℝ)-n)*h by
        have hc : (n:ℝ)+1≤N := by exact_mod_cast Finset.mem_range.mp hn
        nlinarith))
  dsimp only at hb
  simp only [hx,hj] at hb
  rw [Finset.sum_add_distrib,Finset.sum_sub_distrib] at hb
  exact hb

theorem verlet_node_transfer {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (μ : ProbabilityMeasure (E×E)) (hμ : MemLp id 2 (μ : Measure (E×E)))
    (hK : klDiv (μ : Measure (E×E)) (phaseGibbs U)≠∞)
    {h : ℝ} (hh : 0<h) (N : ℕ) :
    let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
    let ν := fun n σ=>(flightLaw (gradient U) hg μ h n σ : Measure (E×E))
    let J := fun n σ=>(klDiv (ν n σ) (phaseGibbs U)).toReal
    let X := fun n σ=>(klDiv (ν n σ).fst (positionGibbs U)).toReal
    (∑n∈Finset.range N,triangularWeight h N n*(X n 0+X n h))≤
      (∑n∈Finset.range N,∫σ in (0:ℝ)..h,(((N:ℝ)-n)*h-σ)*X n σ)-
      (∑n∈Finset.range N,∫σ in (0:ℝ)..h,(((N:ℝ)-n)*h-σ)*J n σ)+
      (∑n∈Finset.range N,triangularWeight h N n*(J n 0+J n h)) :=
  verlet_node_transfer_of_interpolation
    (fun μ _ hh _ _ hσ => freeTransport_interval (μ : Measure (E × E)) hh hσ.1 hσ.2)
    a μ hμ hK hh N

theorem verlet_endpoint_entropy_sum {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (μ : ProbabilityMeasure (E×E)) (hμ : MemLp id 2 (μ : Measure (E×E)))
    (hK : klDiv (μ : Measure (E×E)) (phaseGibbs U)≠∞) (h : ℝ) (N : ℕ) :
    let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
    let ζ := fun n=>(trajectoryLaw (gradient U) hg μ h n : Measure (E×E))
    let ν := fun n σ=>(flightLaw (gradient U) hg μ h n σ : Measure (E×E))
    let e := fun n=>(klDiv (ζ n) (phaseGibbs U)).toReal+
      (∫z,modifiedEnergy U (gradient U) h z-phaseEnergy U z ∂ζ n)
    let Q := fun n=>∫z,cellRemainder U (gradient U) h h z ∂ζ n
    (∑n∈Finset.range N,triangularWeight h N n*
      ((klDiv (ν n 0) (phaseGibbs U)).toReal+(klDiv (ν n h) (phaseGibbs U)).toReal))=
      2*(∑n∈Finset.range N,triangularWeight h N n*e n)+
        (∑n∈Finset.range N,triangularWeight h N n*Q n) := by
  dsimp only
  let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
  let ζ := fun n=>(trajectoryLaw (gradient U) hg μ h n : Measure (E×E))
  have he (n : ℕ) := cell_endpoint_entropy_sum a (ζ n)
    (trajectoryLaw_memLp a μ hμ h n) (trajectoryLaw_entropy_finite a μ hμ hK h n) h
  change (∑n∈Finset.range N,triangularWeight h N n*
    ((klDiv ((ζ n).map (cellState (gradient U) h 0)) (phaseGibbs U)).toReal+
      (klDiv ((ζ n).map (cellState (gradient U) h h)) (phaseGibbs U)).toReal))=_
  rw [Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  rw [he]
  dsimp only [ζ]
  ring

end BreakingResonance
