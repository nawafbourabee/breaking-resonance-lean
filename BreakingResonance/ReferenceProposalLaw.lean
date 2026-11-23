import BreakingResonance.ProposalEntropy
import BreakingResonance.RoundedCountCells
import BreakingResonance.ConditionedGibbs

noncomputable section

open MeasureTheory ProbabilityTheory Set PersistencePays
open scoped ENNReal BigOperators

namespace BreakingResonance

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def attachCount (y : (E×E)×ℕ) : E × (ℕ×E) :=
  (y.1.1,(y.2,y.1.2))

theorem measurable_attachCount : Measurable (attachCount (E := E)) :=
  measurable_fst.fst.prodMk (measurable_snd.prodMk measurable_fst.snd)

theorem attachCount_measurePreserving (U : E → ℝ) (q : Measure ℕ) [IsProbabilityMeasure q] :
    MeasurePreserving attachCount ((phaseGibbs U).prod q)
      ((positionGibbs U).prod (q.prod (stdGaussian E))) := by
  have hs : MeasurePreserving Prod.swap ((stdGaussian E).prod q) (q.prod (stdGaussian E)) :=
    Measure.measurePreserving_swap
  exact ((MeasurePreserving.id (positionGibbs U)).prod hs).comp
    (measurePreserving_prodAssoc (positionGibbs U) (stdGaussian E) q)

theorem attachCount_condition (U : E → ℝ) (q : Measure ℕ) [IsProbabilityMeasure q]
    (E₀ : Set (E×E)) (hE : MeasurableSet E₀) :
    cond ((positionGibbs U).prod (q.prod (stdGaussian E)))
        {z | (z.1,z.2.2) ∈ E₀} =
      ((cond (phaseGibbs U) E₀).prod q).map attachCount := by
  let μ := phaseGibbs U
  let D : Set (E×(ℕ×E)) := {z | (z.1,z.2.2) ∈ E₀}
  let ν := (positionGibbs U).prod (q.prod (stdGaussian E))
  have hD : MeasurableSet D := hE.preimage (measurable_fst.prodMk measurable_snd.snd)
  have hmp := (attachCount_measurePreserving U q).map_eq
  have hpre : attachCount ⁻¹' D = E₀ ×ˢ (univ : Set ℕ) := by ext y; simp [D,attachCount]
  have hmass : ν D = μ E₀ := by
    change (positionGibbs U).prod (q.prod (stdGaussian E)) D = _
    rw [← hmp,Measure.map_apply measurable_attachCount hD,hpre,Measure.prod_prod,measure_univ,mul_one]
  have hr := Measure.restrict_map (μ := μ.prod q) measurable_attachCount hD
  rw [hmp,hpre] at hr
  change cond ν D = ((cond μ E₀).prod q).map attachCount
  rw [ProbabilityTheory.cond,ProbabilityTheory.cond,Measure.prod_smul_left,Measure.map_smul,hmass]
  congr 1
  rw [Measure.restrict_prod_eq_prod_univ]
  exact hr

/-- An independent triangular count, attached to an arbitrary input law,
has exactly the endpoint mixture used in Proposition 6.8. -/
theorem triangular_attached_proposal (g : E → E) (hg : Measurable g)
    (μ : ProbabilityMeasure (E×E)) {h : ℝ} (hh : 0 < h) (N : ℕ) :
    let μx := fun j : ℕ => (⟨(trajectoryLaw g hg μ h j : Measure (E×E)).fst,
      inferInstance⟩ : ProbabilityMeasure E)
    (((μ : Measure (E×E)).prod (triangularCountLaw h N)).map attachCount).map
      (verletProposal g h) = triangularEndpointLaw μx h N := by
  let F := verletProposal g h ∘ attachCount
  have hF : Measurable F := (measurable_verletProposal g hg h).comp measurable_attachCount
  rw [Measure.map_map (measurable_verletProposal g hg h) measurable_attachCount]
  ext A hA
  rw [Measure.map_apply hF hA, Measure.prod_apply_symm (hA.preimage hF)]
  rw [triangularCount_eq_endpointLaw hh]
  unfold triangularEndpointLaw
  rw [lintegral_finsetSum_measure]
  simp only [Measure.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro j hj
  rw [lintegral_smul_measure,smul_eq_mul,Measure.smul_apply,smul_eq_mul]
  let w := ENNReal.ofReal (triangularWeight h N j.1 / ((N:ℝ)*h)^2)
  change w * (∫⁻ k : ℕ, (μ : Measure (E×E)) ((fun z => (z,k)) ⁻¹' (F ⁻¹' A))
      ∂Measure.dirac (j.1+j.2)) =
    w * ((trajectoryLaw g hg μ h (j.1+j.2) : Measure (E×E)).fst A)
  rw [lintegral_dirac]
  congr 1
  rw [Measure.fst_apply hA,show (trajectoryLaw g hg μ h (j.1+j.2) : Measure (E×E)) =
    (μ : Measure (E×E)).map (fun z => trajectory g h z (j.1+j.2)) from rfl,
    Measure.map_apply (trajectory_measurePreserving g hg h (j.1+j.2)).measurable
      (hA.preimage measurable_fst)]
  rfl

end BreakingResonance

#print axioms BreakingResonance.attachCount_condition
#print axioms BreakingResonance.triangular_attached_proposal
