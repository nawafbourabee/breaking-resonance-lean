import BreakingResonance.KernelQuadratic
import BreakingResonance.LevelQuadratic

/-! Comparison and the lower bound for quadratic forms of the actual
Metropolis-adjusted position kernels in Lemma 5.2. -/
noncomputable section
namespace BreakingResonance
open MeasureTheory ProbabilityTheory PersistencePays Set
open scoped ENNReal ProbabilityTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

local notation "μ" => (Measure.prod (volume : Measure E) (volume : Measure E))

def rejectedVerletDensity (U : E → ℝ) (g : E → E) (h : ℝ) (j : ℕ) (z : E × E) : ℝ≥0∞ :=
  phaseGibbsDensity U z - acceptedWeight (phaseGibbsDensity U) (fun z => trajectory g h z j) z

/-- The integral of the squared position test function against the rejected
part of the joint law, averaged over the count law. -/
def verletRejectionForm (U : E → ℝ) (g : E → E) (h : ℝ) (w : Measure ℕ) (f : E → ℝ) : ℝ :=
  ∑' j, countLawWeight w j * (∫ z, f z.1 ^ 2 ∂(μ).withDensity (rejectedVerletDensity U g h j))

theorem verletRejectionForm_nonneg (U : E → ℝ) (g : E → E) (h : ℝ) (w : Measure ℕ)
    (f : E → ℝ) : 0 ≤ verletRejectionForm U g h w f :=
  tsum_nonneg fun j => mul_nonneg (countLawWeight_nonneg w j) (integral_nonneg fun _ => sq_nonneg _)

theorem rejectedVerletDensity_integral (U : E → ℝ) (hU : Measurable U)
    (hi : Integrable (fun x => Real.exp (-U x)) volume)
    (g : E → E) (hg : Measurable g) (h : ℝ) (j : ℕ) (f : E → ℝ) :
    (∫ z, f z.1 ^ 2 ∂(μ).withDensity (rejectedVerletDensity U g h j)) =
      ∫ z, (rejectedVerletDensity U g h j z).toReal * f z.1 ^ 2 ∂μ := by
  let p := phaseGibbsDensity U
  have hp : Measurable p := phaseGibbsDensity_measurable U hU
  have hT := trajectory_measurePreserving g hg h j
  have hr : Measurable (rejectedVerletDensity U g h j) :=
    hp.sub (hp.min (hp.comp hT.measurable))
  have hf : ∀ᵐ z ∂μ, rejectedVerletDensity U g h j z < ∞ :=
    Filter.Eventually.of_forall fun z =>
      lt_of_le_of_lt tsub_le_self (lt_top_iff_ne_top.mpr (phaseGibbsDensity_ne_top U hi z))
  rw [integral_withDensity_eq_integral_toReal_smul hr hf]
  simp only [smul_eq_mul]

theorem phaseDensity_position_memLp (U : E → ℝ) (hU : Measurable U)
    (hi : Integrable (fun x => Real.exp (-U x)) volume)
    (f : E → ℝ) (hf : MemLp f 2 (positionGibbs U)) :
    MemLp (f ∘ (Prod.fst : E × E → E)) 2 ((μ).withDensity (phaseGibbsDensity U)) := by
  rw [← phaseGibbs_eq_withDensity U hU hi]
  exact hf.comp_measurePreserving measurePreserving_fst

theorem phaseDensity_position_sq (U : E → ℝ) (hU : Measurable U)
    (hi : Integrable (fun x => Real.exp (-U x)) volume)
    (f : E → ℝ) (hf : MemLp f 2 (positionGibbs U)) :
    (∫ z, f z.1 ^ 2 ∂(μ).withDensity (phaseGibbsDensity U)) = ∫ x, f x ^ 2 ∂positionGibbs U := by
  rw [← phaseGibbs_eq_withDensity U hU hi]
  have hfst : MeasurePreserving Prod.fst (phaseGibbs U) (positionGibbs U) :=
    measurePreserving_fst
  calc
    _ = ∫ x, f x ^ 2 ∂(phaseGibbs U).map Prod.fst :=
      (integral_map hfst.measurable.aemeasurable
        (hfst.map_eq.symm ▸ (hf.aestronglyMeasurable.aemeasurable.pow_const 2).aestronglyMeasurable)).symm
    _ = _ := by rw [hfst.map_eq]

theorem summable_verletRejectionForm (U : E → ℝ) (hU : Measurable U)
    (hi : Integrable (fun x => Real.exp (-U x)) volume)
    (g : E → E) (h : ℝ) (w : Measure ℕ) [IsProbabilityMeasure w]
    (f : E → ℝ) (hf : Measurable f) (hf₂ : MemLp f 2 (positionGibbs U)) :
    Summable fun j => countLawWeight w j *
      (∫ z, f z.1 ^ 2 ∂(μ).withDensity (rejectedVerletDensity U g h j)) := by
  let ν := (μ).withDensity (phaseGibbsDensity U)
  have hsq : Integrable (fun z : E × E => f z.1 ^ 2) ν :=
    (memLp_two_iff_integrable_sq (hf.comp measurable_fst).aestronglyMeasurable).mp
      (phaseDensity_position_memLp U hU hi f hf₂)
  apply ((countLawWeight_summable w).mul_right (∫ z, f z.1 ^ 2 ∂ν)).of_norm_bounded
  intro j
  rw [Real.norm_of_nonneg (mul_nonneg (countLawWeight_nonneg w j)
    (integral_nonneg fun _ => sq_nonneg _))]
  apply mul_le_mul_of_nonneg_left _ (countLawWeight_nonneg w j)
  exact integral_mono_measure (withDensity_mono (Filter.Eventually.of_forall (fun _ => tsub_le_self)))
    (Filter.Eventually.of_forall (fun _ => sq_nonneg _)) hsq

set_option maxHeartbeats 1000000 in
theorem randomizedVerletKernel_quadratic_levels (U : E → ℝ) (hU : Measurable U)
    (hi : Integrable (fun x => Real.exp (-U x)) volume)
    (g : E → E) (hg : Measurable g) (h : ℝ) (w : Measure ℕ) [IsProbabilityMeasure w]
    (f : E → ℝ) (hf : Measurable f) (hf₂ : MemLp f 2 (positionGibbs U)) :
    integratedCosineForm μ (phaseGibbsDensity U) (phaseGibbsDensity_ne_top U hi)
      (phaseGibbsDensity_measurable U hU) (f ∘ Prod.fst) (hf.comp measurable_fst)
      (phaseDensity_position_memLp U hU hi f hf₂) (trajectoryEquiv g hg h 1)
      (trajectory_measurePreserving g hg h 1) (countLawWeight w) +
      verletRejectionForm U g h w f =
        kernelQuadratic (positionGibbs U) (randomizedVerletKernel U hU g hg h w) f := by
  let : IsProbabilityMeasure (positionGibbs U) := isProbabilityMeasure_tilted hi
  let p := phaseGibbsDensity U
  let F := trajectoryEquiv g hg h 1
  let fₛ := f ∘ (Prod.fst : E × E → E)
  have hp := phaseGibbsDensity_ne_top U hi
  have hpm := phaseGibbsDensity_measurable U hU
  have hfm : Measurable fₛ := hf.comp measurable_fst
  have hfs := phaseDensity_position_memLp U hU hi f hf₂
  have hF : MeasurePreserving F μ μ := trajectory_measurePreserving g hg h 1
  let A (j : ℕ) := ∫ u : ℝ, levelCross μ p fₛ F j u
  let R (j : ℕ) := ∫ z, f z.1 ^ 2 ∂(μ).withDensity (rejectedVerletDensity U g h j)
  have hFj (j : ℕ) (z : E × E) : (F : E × E → E × E)^[j] z = trajectory g h z j := by
    change ((verlet g h)^[1])^[j] z = _
    simp [trajectory]
  have hfixed (j : ℕ) :
      kernelQuadratic (positionGibbs U) (fixedVerletKernel U hU g hg h j) f = A j + R j := by
    rw [kernelQuadratic, fixedVerletKernel_quadratic_levels U hU hi g hg h j f hf hf₂]
    congr 1
    dsimp only [A, levelCross, fₛ, Function.comp_apply]
    apply integral_congr_ae
    filter_upwards with u
    apply integral_congr_ae
    filter_upwards with z
    rw [hFj]
    by_cases hz : u ∈ Ioc 0 (p z).toReal <;>
      by_cases ht : u ∈ Ioc 0 (p (trajectory g h z j)).toReal <;>
      simp [p, densityTest, indicator, hz, ht]
  have hA : Summable fun j => countLawWeight w j * A j := by
    have hb := summable_levelCross_integral_norm μ p hp hpm fₛ hfm hfs F hF
      (countLawWeight w) (countLawWeight_nonneg w) (countLawWeight_summable w)
    apply hb.of_norm_bounded
    intro j
    rw [show countLawWeight w j * A j = ∫ u : ℝ, countLawWeight w j * levelCross μ p fₛ F j u
      from (integral_const_mul _ _).symm]
    exact norm_integral_le_integral_norm _
  have hR : Summable fun j => countLawWeight w j * R j :=
    summable_verletRejectionForm U hU hi g h w f hf hf₂
  let P := randomizedVerletKernel U hU g hg h w
  have hP : P.Invariant (positionGibbs U) :=
    (randomizedVerletKernel_reversible U hU hi g hg h w).invariant
  have hm := kernelQuadratic_countable_mixture (positionGibbs U) P hP
    (fixedVerletKernel U hU g hg h) w (randomizedVerletKernel_mixture U hU g hg h w) f hf₂
  change integratedCosineForm μ p hp hpm fₛ hfm hfs F hF (countLawWeight w) +
    verletRejectionForm U g h w f = kernelQuadratic (positionGibbs U) P f
  rw [integratedCosineForm_eq_tsum μ p hp hpm fₛ hfm hfs F hF (countLawWeight w)
    (countLawWeight_nonneg w) (countLawWeight_summable w), ← hm.tsum_eq]
  change (∑' j, countLawWeight w j * A j) + (∑' j, countLawWeight w j * R j) = _
  rw [← hA.tsum_add hR]
  apply tsum_congr
  intro j
  rw [hfixed, mul_add]

/-- The lower spectral inequality of Lemma 5.2, written as a quadratic form. -/
theorem randomizedVerletKernel_lower_borel (U : E → ℝ) (hU : Measurable U)
    (hi : Integrable (fun x => Real.exp (-U x)) volume)
    (g : E → E) (hg : Measurable g) (h : ℝ) (w : Measure ℕ) [IsProbabilityMeasure w]
    (β : ℝ) (hβ : ∀ θ ∈ Icc (-Real.pi) Real.pi, -1 + β ≤ cosineSeries (countLawWeight w) θ)
    (f : E → ℝ) (hf : Measurable f) (hf₂ : MemLp f 2 (positionGibbs U)) :
    (-1 + β) * (∫ x, f x ^ 2 ∂positionGibbs U) ≤
      kernelQuadratic (positionGibbs U) (randomizedVerletKernel U hU g hg h w) f := by
  have hlower := integratedCosineForm_lower μ (phaseGibbsDensity U)
    (phaseGibbsDensity_ne_top U hi) (phaseGibbsDensity_measurable U hU)
    (f ∘ Prod.fst) (hf.comp measurable_fst) (phaseDensity_position_memLp U hU hi f hf₂)
    (trajectoryEquiv g hg h 1) (trajectory_measurePreserving g hg h 1)
    (countLawWeight w) (countLawWeight_nonneg w) (countLawWeight_summable w) β hβ
  change (-1 + β) * (∫ z, f z.1 ^ 2 ∂(μ).withDensity (phaseGibbsDensity U)) ≤ _ at hlower
  rw [phaseDensity_position_sq U hU hi f hf₂] at hlower
  rw [← randomizedVerletKernel_quadratic_levels U hU hi g hg h w f hf hf₂]
  exact hlower.trans (le_add_of_nonneg_right (verletRejectionForm_nonneg U g h w f))

/-- The Dirichlet form comparison of Lemma 5.2, with its rejection term. -/
theorem randomizedVerletKernel_comparison_borel (U : E → ℝ) (hU : Measurable U)
    (hi : Integrable (fun x => Real.exp (-U x)) volume) (g : E → E) (hg : Measurable g)
    (h : ℝ) (w q : Measure ℕ) [IsProbabilityMeasure w] [IsProbabilityMeasure q]
    (c : ℝ) (hc : 0 < c) (hcompare : ∀ θ ∈ Icc (-Real.pi) Real.pi,
      c * (1 - cosineSeries (countLawWeight q) θ) ≤ 1 - cosineSeries (countLawWeight w) θ)
    (f : E → ℝ) (hf : Measurable f) (hf₂ : MemLp f 2 (positionGibbs U)) :
    let N := ∫ x, f x ^ 2 ∂positionGibbs U
    c * (N - kernelQuadratic (positionGibbs U) (randomizedVerletKernel U hU g hg h q) f) -
      verletRejectionForm U g h w f ≤
      N - kernelQuadratic (positionGibbs U) (randomizedVerletKernel U hU g hg h w) f := by
  dsimp only
  have hbound := integratedCosineForm_comparison μ (phaseGibbsDensity U)
    (phaseGibbsDensity_ne_top U hi) (phaseGibbsDensity_measurable U hU)
    (f ∘ Prod.fst) (hf.comp measurable_fst) (phaseDensity_position_memLp U hU hi f hf₂)
    (trajectoryEquiv g hg h 1) (trajectory_measurePreserving g hg h 1)
    (countLawWeight w) (countLawWeight q) (countLawWeight_nonneg w) (countLawWeight_nonneg q)
    (countLawWeight_summable w) (countLawWeight_summable q) c hcompare
  dsimp only [Function.comp_apply] at hbound
  rw [phaseDensity_position_sq U hU hi f hf₂] at hbound
  rw [← randomizedVerletKernel_quadratic_levels U hU hi g hg h w f hf hf₂,
    ← randomizedVerletKernel_quadratic_levels U hU hi g hg h q f hf hf₂]
  have hr := mul_nonneg hc.le (verletRejectionForm_nonneg U g h q f)
  linarith only [hbound, hr]

theorem verletRejectionForm_congr (U : E → ℝ) (hU : Measurable U)
    (hi : Integrable (fun x => Real.exp (-U x)) volume)
    (g : E → E) (h : ℝ) (w : Measure ℕ)
    {f k : E → ℝ} (heq : f =ᵐ[positionGibbs U] k) :
    verletRejectionForm U g h w f = verletRejectionForm U g h w k := by
  have hfst : MeasurePreserving Prod.fst (phaseGibbs U) (positionGibbs U) :=
    measurePreserving_fst
  have he := hfst.quasiMeasurePreserving.ae_eq_comp heq
  rw [phaseGibbs_eq_withDensity U hU hi] at he
  apply tsum_congr
  intro j
  congr 1
  apply integral_congr_ae
  have hle : (μ).withDensity (rejectedVerletDensity U g h j) ≤
      (μ).withDensity (phaseGibbsDensity U) :=
    withDensity_mono (Filter.Eventually.of_forall (fun _ => tsub_le_self))
  filter_upwards [ae_mono hle he] with z hz
  exact congrArg (· ^ 2) hz

/-- Lemma 5.2, lower spectral bound on real L² of the position Gibbs law. -/
theorem randomizedVerletKernel_lower_l2 (U : E → ℝ) (hU : Measurable U)
    (hi : Integrable (fun x => Real.exp (-U x)) volume)
    (g : E → E) (hg : Measurable g) (h : ℝ) (w : Measure ℕ) [IsProbabilityMeasure w]
    (β : ℝ) (hβ : ∀ θ ∈ Icc (-Real.pi) Real.pi, -1 + β ≤ cosineSeries (countLawWeight w) θ)
    (f : Lp ℝ 2 (positionGibbs U)) :
    (-1 + β) * (∫ x, f x ^ 2 ∂positionGibbs U) ≤
      kernelQuadratic (positionGibbs U) (randomizedVerletKernel U hU g hg h w) f := by
  let : IsProbabilityMeasure (positionGibbs U) := isProbabilityMeasure_tilted hi
  let f₀ := (Lp.memLp f).aestronglyMeasurable.mk f
  have he : (f : E → ℝ) =ᵐ[positionGibbs U] f₀ := (Lp.memLp f).aestronglyMeasurable.ae_eq_mk
  have hn : (∫ x, f x ^ 2 ∂positionGibbs U) = ∫ x, f₀ x ^ 2 ∂positionGibbs U :=
    integral_congr_ae (he.mono fun _ hx => congrArg (· ^ 2) hx)
  have hP := (randomizedVerletKernel_reversible U hU hi g hg h w).invariant
  rw [hn, kernelQuadratic_congr _ _ hP he]
  exact randomizedVerletKernel_lower_borel U hU hi g hg h w β hβ f₀
    (Lp.memLp f).aestronglyMeasurable.measurable_mk (MemLp.ae_eq he (Lp.memLp f))

/-- Lemma 5.2, comparison on real L² of the position Gibbs law. -/
theorem randomizedVerletKernel_comparison_l2 (U : E → ℝ) (hU : Measurable U)
    (hi : Integrable (fun x => Real.exp (-U x)) volume) (g : E → E) (hg : Measurable g)
    (h : ℝ) (w q : Measure ℕ) [IsProbabilityMeasure w] [IsProbabilityMeasure q]
    (c : ℝ) (hc : 0 < c) (hcompare : ∀ θ ∈ Icc (-Real.pi) Real.pi,
      c * (1 - cosineSeries (countLawWeight q) θ) ≤ 1 - cosineSeries (countLawWeight w) θ)
    (f : Lp ℝ 2 (positionGibbs U)) :
    let N := ∫ x, f x ^ 2 ∂positionGibbs U
    c * (N - kernelQuadratic (positionGibbs U) (randomizedVerletKernel U hU g hg h q) f) -
      verletRejectionForm U g h w f ≤
      N - kernelQuadratic (positionGibbs U) (randomizedVerletKernel U hU g hg h w) f := by
  dsimp only
  let : IsProbabilityMeasure (positionGibbs U) := isProbabilityMeasure_tilted hi
  let f₀ := (Lp.memLp f).aestronglyMeasurable.mk f
  have he : (f : E → ℝ) =ᵐ[positionGibbs U] f₀ := (Lp.memLp f).aestronglyMeasurable.ae_eq_mk
  have hn : (∫ x, f x ^ 2 ∂positionGibbs U) = ∫ x, f₀ x ^ 2 ∂positionGibbs U :=
    integral_congr_ae (he.mono fun _ hx => congrArg (· ^ 2) hx)
  have hw := (randomizedVerletKernel_reversible U hU hi g hg h w).invariant
  have hq := (randomizedVerletKernel_reversible U hU hi g hg h q).invariant
  rw [hn, kernelQuadratic_congr _ _ hq he, kernelQuadratic_congr _ _ hw he,
    verletRejectionForm_congr U hU hi g h w he]
  exact randomizedVerletKernel_comparison_borel U hU hi g hg h w q c hc hcompare f₀
    (Lp.memLp f).aestronglyMeasurable.measurable_mk (MemLp.ae_eq he (Lp.memLp f))

end BreakingResonance

#print axioms BreakingResonance.randomizedVerletKernel_quadratic_levels
#print axioms BreakingResonance.randomizedVerletKernel_lower_borel
#print axioms BreakingResonance.randomizedVerletKernel_comparison_borel
#print axioms BreakingResonance.randomizedVerletKernel_lower_l2
#print axioms BreakingResonance.randomizedVerletKernel_comparison_l2
