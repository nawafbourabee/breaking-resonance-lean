import BreakingResonance.AdjustedComparison
import BreakingResonance.IndicatorFlow
import BreakingResonance.RoundedFourierBounds
import BreakingResonance.RestrictedLevelSets

noncomputable section

open MeasureTheory ProbabilityTheory Set PersistencePays
open scoped ENNReal ProbabilityTheory

namespace BreakingResonance

theorem roundedDurationLaw_mono (h : ℝ) {ρ ν : Measure ℝ} (hle : ρ ≤ ν) :
    roundedDurationLaw h ρ ≤ roundedDurationLaw h ν := by
  apply Measure.le_iff.mpr
  intro A hA
  simp only [roundedDurationLaw, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  exact add_le_add (mul_le_mul' le_rfl (Measure.map_mono hle (measurable_floorDuration h) A))
    (mul_le_mul' le_rfl (Measure.map_mono hle (measurable_succFloorDuration h) A))

theorem roundedDurationLaw_smul (h : ℝ) (p : ℝ≥0∞) (ρ : Measure ℝ) :
    roundedDurationLaw h (p • ρ) = p • roundedDurationLaw h ρ := by
  unfold roundedDurationLaw
  rw [Measure.map_smul,Measure.map_smul,smul_add,smul_smul,smul_smul,smul_smul,smul_smul,
    mul_comm p ((1:ℝ≥0∞)/2)]

theorem weighted_roundedConditional_le (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    (h τstar : ℝ) (hp : ρ (Iic τstar) ≠ 0) :
    ρ (Iic τstar) • roundedDurationLaw h (conditionalDurationLaw ρ τstar) ≤ roundedDurationLaw h ρ := by
  rw [← roundedDurationLaw_smul,conditionalDurationLaw,smul_smul,
    ENNReal.mul_inv_cancel hp (measure_ne_top ρ _),one_smul]
  exact roundedDurationLaw_mono h Measure.restrict_le_self

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem weighted_mixture_flow_le (U : E → ℝ) (hU : Measurable U)
    (g : E → E) (hg : Measurable g) (h : ℝ)
    (w q : Measure ℕ) [IsProbabilityMeasure w] [IsProbabilityMeasure q]
    (p : ℝ≥0∞) (hweight : p • w ≤ q) (π : Measure E) [IsProbabilityMeasure π]
    {A : Set E} (hA : MeasurableSet A) :
    p*(π ⊗ₘ randomizedVerletKernel U hU g hg h w) (A×ˢ Aᶜ) ≤
      (π ⊗ₘ randomizedVerletKernel U hU g hg h q) (A×ˢ Aᶜ) := by
  rw [Measure.compProd_apply_prod hA hA.compl,Measure.compProd_apply_prod hA hA.compl,
    ← lintegral_const_mul _ ((randomizedVerletKernel U hU g hg h w).measurable_coe hA.compl)]
  apply lintegral_mono
  intro x
  change p*(randomizedVerletKernel U hU g hg h w x Aᶜ) ≤ randomizedVerletKernel U hU g hg h q x Aᶜ
  rw [randomizedVerletKernel_mixture U hU g hg h w x Aᶜ hA.compl,
    randomizedVerletKernel_mixture U hU g hg h q x Aᶜ hA.compl]
  calc
    _ = ∫⁻ j, fixedVerletKernel U hU g hg h j x Aᶜ ∂(p • w) := by
      rw [lintegral_smul_measure,smul_eq_mul]
    _ ≤ _ := lintegral_mono' hweight le_rfl

/-- Transfer from the triangular reference flow through the conditional
count law, with the phase space rejection form subtracted. -/
theorem transfer_restricted_conductance (U : E → ℝ) (hU : Measurable U)
    (hZ : Integrable (fun x => Real.exp (-U x)) volume)
    (g : E → E) (hg : Measurable g) (h : ℝ)
    (ρ : Measure ℝ) [IsProbabilityMeasure ρ] (τstar : ℝ) (hp : ρ (Iic τstar) ≠ 0)
    (q : Measure ℕ) [IsProbabilityMeasure q] {s c : ℝ} (hc : 0 < c)
    (hcompare : ∀ θ ∈ Icc (-Real.pi) Real.pi,
      c*(1-cosineSeries (countLawWeight q) θ) ≤
        1-cosineSeries (countLawWeight (roundedDurationLaw h (conditionalDurationLaw ρ τstar))) θ)
    (href : RestrictedConductance (positionGibbs U) (randomizedVerletKernel U hU g hg h q) s (1/50))
    (hrej : ∀ A : Set E, MeasurableSet A → ENNReal.ofReal s ≤ positionGibbs U A →
      positionGibbs U A ≤ 1/2 →
      verletRejectionForm U g h (roundedDurationLaw h (conditionalDurationLaw ρ τstar))
        (A.indicator (fun _ => 1)) ≤ (c/300)*(positionGibbs U).real A) :
    RestrictedConductance (positionGibbs U) (roundedVerletKernel U hU g hg h ρ) s
      ((ρ (Iic τstar)).toReal*c/60) := by
  let π := positionGibbs U
  let : IsProbabilityMeasure π := isProbabilityMeasure_tilted hZ
  let : IsProbabilityMeasure (conditionalDurationLaw ρ τstar) :=
    conditionalDuration_isProbability ρ τstar hp
  let w := roundedDurationLaw h (conditionalDurationLaw ρ τstar)
  let P := roundedVerletKernel U hU g hg h ρ
  let Pw := randomizedVerletKernel U hU g hg h w
  let Pq := randomizedVerletKernel U hU g hg h q
  intro A hA hsA hAh
  let f := A.indicator (fun _ : E => (1:ℝ))
  have hf : Measurable f := measurable_const.indicator hA
  have hfl : MemLp f 2 π := indicator_one_memLp π hA
  have hwe := indicator_kernel_flow π Pw hA
  have hqe := indicator_kernel_flow π Pq hA
  dsimp only at hwe hqe
  have hcmp := randomizedVerletKernel_comparison_borel U hU hZ g hg h w q c hc hcompare f hf hfl
  dsimp only at hcmp
  change c*((∫ x, (f x)^2 ∂π)-kernelQuadratic π Pq f)-verletRejectionForm U g h w f ≤
    (∫ x, (f x)^2 ∂π)-kernelQuadratic π Pw f at hcmp
  rw [hwe,hqe] at hcmp
  have hq0 := ENNReal.toReal_mono (measure_ne_top (π ⊗ₘ Pq) _) (href A hA hsA hAh)
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ 1/50)] at hq0
  change (1/50)*π.real A ≤ (π ⊗ₘ Pq).real (A×ˢ Aᶜ) at hq0
  have hw0 : c/60*π.real A ≤ (π ⊗ₘ Pw).real (A×ˢ Aᶜ) := by
    have hm := mul_le_mul_of_nonneg_left hq0 hc.le
    have hd : verletRejectionForm U g h w f ≤ (c/300)*π.real A := hrej A hA hsA hAh
    linarith only [hcmp,hm,hd]
  have hbig := weighted_mixture_flow_le U hU g hg h w (roundedDurationLaw h ρ) _
    (weighted_roundedConditional_le ρ h τstar hp) π hA
  have hbig' := ENNReal.toReal_mono (measure_ne_top (π ⊗ₘ P) _) hbig
  rw [ENNReal.toReal_mul] at hbig'
  have hfinal := mul_le_mul_of_nonneg_left hw0 (ENNReal.toReal_nonneg (a := ρ (Iic τstar)))
  change _ ≤ (π ⊗ₘ P) (A×ˢ Aᶜ)
  have hpos : 0 ≤ (ρ (Iic τstar)).toReal*c/60 := by positivity
  rw [← ENNReal.ofReal_toReal (measure_ne_top π A),← ENNReal.ofReal_mul hpos,
    ← ENNReal.ofReal_toReal (measure_ne_top (π ⊗ₘ P) (A×ˢ Aᶜ))]
  apply ENNReal.ofReal_le_ofReal
  change (ρ (Iic τstar)).toReal*(π ⊗ₘ Pw).real (A×ˢ Aᶜ) ≤
    (π ⊗ₘ P).real (A×ˢ Aᶜ) at hbig'
  change ((ρ (Iic τstar)).toReal*c/60)*π.real A ≤ (π ⊗ₘ P).real (A×ˢ Aᶜ)
  nlinarith only [hbig',hfinal]

end BreakingResonance

#print axioms BreakingResonance.transfer_restricted_conductance
