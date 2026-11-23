import BreakingResonance.GaussianDiagonalTarget
import BreakingResonance.Reversibility

noncomputable section

open MeasureTheory ProbabilityTheory Set PersistencePays
open scoped ENNReal ProbabilityTheory

namespace BreakingResonance

def stationaryCrossing {S : Type*} [MeasurableSpace S]
    (π : Measure S) (P : Kernel S S) (A : Set S) : ℝ≥0∞ :=
  ∫⁻ x in A, P x Aᶜ ∂π

theorem verletCrossing_le_proposal
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (U : E → ℝ) (hU : Measurable U) (g : E → E) (hg : Measurable g)
    (h : ℝ) (j : ℕ) (A : Set E) (hA : MeasurableSet A) :
    stationaryCrossing (positionGibbs U) (fixedVerletKernel U hU g hg h j) A ≤
      phaseGibbs U {z | z.1 ∈ A ∧ (trajectory g h z j).1 ∉ A} := by
  let π := positionGibbs U
  let γ := stdGaussian E
  let F (z : E×E) := (trajectory g h z j).1
  let B : Set (E×E) := {z | z.1 ∈ A ∧ F z ∉ A}
  have hF : Measurable F := (trajectory_measurePreserving g hg h j).measurable.fst
  have hB : MeasurableSet B := (hA.preimage measurable_fst).inter (hA.compl.preimage hF)
  change stationaryCrossing π (fixedVerletKernel U hU g hg h j) A ≤ π.prod γ B
  rw [Measure.prod_apply hB,stationaryCrossing,← lintegral_indicator hA]
  apply lintegral_mono
  intro x
  by_cases hx : x ∈ A
  · let V : Set E := (Prod.mk x) ⁻¹' B
    have hV : MeasurableSet V := hB.preimage measurable_prodMk_left
    rw [indicator_of_mem hx,fixedVerletKernel,proposalKernel_apply _ _ _ _ _ x Aᶜ hA.compl]
    change _ ≤ γ V
    have hν : (∫⁻ v, V.indicator (fun _ => (1:ℝ≥0∞)) v ∂γ) = γ V := by
      rw [lintegral_indicator_const hV,one_mul]
    rw [← hν]
    apply lintegral_mono
    intro v
    have he : Aᶜ.indicator (fun _ => (1:ℝ≥0∞)) (F (x,v)) = V.indicator (fun _ => 1) v := by
      by_cases hl : F (x,v) ∈ A
      · have hv : v ∉ V := fun hv => hv.2 hl
        rw [indicator_of_notMem (show F (x,v) ∉ Aᶜ from not_not.mpr hl),indicator_of_notMem hv]
      · have hv : v ∈ V := ⟨hx,hl⟩
        rw [indicator_of_mem (show F (x,v) ∈ Aᶜ from hl),indicator_of_mem hv]
    simp only [indicator_of_notMem (show x ∉ Aᶜ from not_not.mpr hx),mul_zero,add_zero]
    change acceptProbability _ (x,v)*Aᶜ.indicator (fun _ => 1) (F (x,v)) ≤ _
    rw [he]
    exact (mul_le_mul_left (acceptProbability_le_one _ _) _).trans_eq (one_mul _)
  · rw [indicator_of_notMem hx]
    exact zero_le

theorem gaussianFixedKernel_crossing {m L h : ℝ} (hm : 0 < m) (hmL : m ≤ L)
    (hh : 0 < h) (hhL : h*Real.sqrt L ≤ 1) (j : ℕ) :
    stationaryCrossing (positionGibbs (diagonalGaussianPotential m L))
      (fixedVerletKernel (diagonalGaussianPotential m L) (diagonalGaussianPotential_measurable m L)
        (diagonalGaussianForce m L) (diagonalGaussianForce_measurable hm hmL) h j)
      gaussianSlowHalfspace ≤ ENNReal.ofReal (2/(3*Real.pi)*(h*Real.sqrt m)*(j:ℝ)) := by
  let U := diagonalGaussianPotential m L
  let g := diagonalGaussianForce m L
  let F (z : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) := (z.1 0,z.2 0)
  let μ := phaseGibbs U
  have hF : MeasurePreserving F μ (phaseGibbs (fastPotential m m)) := gaussianSlowPhase_projection hm hmL
  have hg := diagonalGaussianForce_measurable hm hmL
  let A := gaussianSlowHalfspace
  let B : Set (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) :=
    {z | z.1 ∈ A ∧ (trajectory g h z j).1 ∉ A}
  have hB : MeasurableSet B := (gaussianSlowHalfspace_measurable.preimage measurable_fst).inter
    (gaussianSlowHalfspace_measurable.compl.preimage (trajectory_measurePreserving g hg h j).measurable.fst)
  have he : B = F ⁻¹' scalarVerletCrossing m h j := by
    ext z
    have ht := separableTrajectory (diagonalGaussianCurvature m L) (diagonalGaussianCurvature m L) h z j 0
    simp only [diagonalGaussianCurvature,ite_true] at ht
    have hx := congrArg Prod.fst ht
    change (trajectory g h z j).1 0 = (trajectory (fastGradient m m) h (F z) j).1 at hx
    change (z.1 0 ≤ 0 ∧ ¬ (trajectory g h z j).1 0 ≤ 0) ↔
      ((F z).1 ≤ 0 ∧ 0 < (trajectory (fastGradient m m) h (F z) j).1)
    rw [hx,not_le]
  have hM : μ B = phaseGibbs (fastPotential m m) (scalarVerletCrossing m h j) := by
    rw [he]
    have hMeas : MeasurableSet (scalarVerletCrossing m h j) :=
      (measurableSet_le measurable_fst measurable_const).inter
        (measurableSet_lt measurable_const (trajectory_measurePreserving (fastGradient m m)
          (fastGradient_continuous m m).measurable h j).measurable.fst)
    rw [← Measure.map_apply hF.measurable hMeas,hF.map_eq]
  apply le_trans (verletCrossing_le_proposal _ _ _ _ _ _ _ gaussianSlowHalfspace_measurable)
  change μ B ≤ _
  rw [hM]
  apply scalarVerletCrossing_bound hm hh _ j
  exact (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hmL) hh.le).trans hhL

theorem stationaryCrossing_mixture {S : Type*} [MeasurableSpace S] (π : Measure S)
    [SFinite π] (Q : Kernel S S) (K : ℕ → Kernel S S) (lawJ : Measure ℕ) [SFinite lawJ]
    (A : Set S) (hA : MeasurableSet A)
    (h : ∀ x, Q x Aᶜ = ∫⁻ j, K j x Aᶜ ∂lawJ) :
    stationaryCrossing π Q A = ∫⁻ j, stationaryCrossing π (K j) A ∂lawJ := by
  have hm : Measurable (fun p : S×ℕ => K p.2 p.1 Aᶜ) := by
    apply measurable_from_prod_countable_left
    exact fun j => (K j).measurable_coe hA.compl
  unfold stationaryCrossing
  simp_rw [h]
  exact lintegral_lintegral_swap (μ := π.restrict A) (ν := lawJ)
    (f := fun x j => K j x Aᶜ) hm.aemeasurable

theorem gaussianMixedKernel_crossing {m L h : ℝ} (hm : 0 < m) (hmL : m ≤ L)
    (hh : 0 < h) (hhL : h*Real.sqrt L ≤ 1) (lawJ : Measure ℕ) [IsProbabilityMeasure lawJ]
    (hJ : Integrable (fun j : ℕ => (j:ℝ)) lawJ) :
    stationaryCrossing (positionGibbs (diagonalGaussianPotential m L))
      (randomizedVerletKernel (diagonalGaussianPotential m L) (diagonalGaussianPotential_measurable m L)
        (diagonalGaussianForce m L) (diagonalGaussianForce_measurable hm hmL) h lawJ)
      gaussianSlowHalfspace ≤ ENNReal.ofReal (2/(3*Real.pi)*(h*Real.sqrt m)*(∫ j : ℕ, (j:ℝ) ∂lawJ)) := by
  let U := diagonalGaussianPotential m L
  let g := diagonalGaussianForce m L
  let hg := diagonalGaussianForce_measurable hm hmL
  let hU := diagonalGaussianPotential_measurable m L
  let Q := randomizedVerletKernel U hU g hg h lawJ
  let K (j : ℕ) := fixedVerletKernel U hU g hg h j
  let π := positionGibbs U
  let A := gaussianSlowHalfspace
  let C := 2/(3*Real.pi)*(h*Real.sqrt m)
  have hA := gaussianSlowHalfspace_measurable
  have hM : (fun x => Q x Aᶜ) = fun x => ∫⁻ j, K j x Aᶜ ∂lawJ := by
    funext x
    exact randomizedVerletKernel_mixture U hU g hg h lawJ x _ hA.compl
  have hflow (j : ℕ) : stationaryCrossing π (K j) A ≤ ENNReal.ofReal (C*(j:ℝ)) :=
    gaussianFixedKernel_crossing hm hmL hh hhL j
  have hi : Integrable (fun j : ℕ => C*(j:ℝ)) lawJ := hJ.const_mul _
  have hc : 0 ≤ C := by unfold C; positivity
  have he : (∫⁻ j : ℕ, ENNReal.ofReal (C*(j:ℝ)) ∂lawJ)
      = ENNReal.ofReal (C*(∫ j : ℕ, (j:ℝ) ∂lawJ)) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hi
      (ae_of_all _ (fun j => mul_nonneg hc (Nat.cast_nonneg j))),integral_const_mul]
  change stationaryCrossing π Q A ≤ ENNReal.ofReal (C*(∫ j : ℕ, (j:ℝ) ∂lawJ))
  rw [stationaryCrossing_mixture π Q K lawJ A hA (congrFun hM),← he]
  exact lintegral_mono hflow

end BreakingResonance

#print axioms BreakingResonance.verletCrossing_le_proposal
#print axioms BreakingResonance.gaussianFixedKernel_crossing
#print axioms BreakingResonance.gaussianMixedKernel_crossing
