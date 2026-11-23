import BreakingResonance.RoundingCost

noncomputable section

open MeasureTheory

namespace BreakingResonance

theorem independentCountSum (lawJ : Measure ℕ) [IsProbabilityMeasure lawJ]
    (hJ : Integrable (fun j : ℕ => (j:ℝ)) lawJ) (n : ℕ) :
    let μ := Measure.pi (fun _ : Fin n => lawJ)
    Integrable (fun J : Fin n → ℕ => ∑ i, (J i:ℝ)) μ ∧
      (∫ J : Fin n → ℕ, ∑ i, (J i:ℝ) ∂μ) = (n:ℝ)*(∫ j : ℕ, (j:ℝ) ∂lawJ) := by
  let μ := Measure.pi (fun _ : Fin n => lawJ)
  let g : ℕ → ℝ := fun j => j
  have hg : Measurable g := measurable_of_countable _
  have he (i : Fin n) : MeasurePreserving (Function.eval i) μ lawJ :=
    measurePreserving_eval (fun _ : Fin n => lawJ) i
  have hmap (i : Fin n) : Integrable g (μ.map (Function.eval i)) := by
    rw [(he i).map_eq]
    exact hJ
  have hint (i : Fin n) : Integrable (fun J : Fin n → ℕ => (J i:ℝ)) μ :=
    (integrable_map_measure (hg.aestronglyMeasurable) (he i).measurable.aemeasurable).mp (hmap i)
  have hex (i : Fin n) : (∫ J : Fin n → ℕ, (J i:ℝ) ∂μ) = ∫ j : ℕ, (j:ℝ) ∂lawJ := by
    calc
      _ = ∫ j, g j ∂(μ.map (Function.eval i)) :=
        (integral_map (he i).measurable.aemeasurable hg.aestronglyMeasurable).symm
      _ = _ := by rw [(he i).map_eq]
  refine ⟨integrable_finsetSum _ (fun i _ => hint i),?_⟩
  change (∫ J : Fin n → ℕ, ∑ i, (J i:ℝ) ∂μ) = _
  rw [integral_finsetSum _ (fun i _ => hint i)]
  simp_rw [hex]
  simp [nsmul_eq_mul]

end BreakingResonance

#print axioms BreakingResonance.independentCountSum
