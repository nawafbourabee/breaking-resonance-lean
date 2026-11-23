import BreakingResonance.AdjustedFlow
import BreakingResonance.FourierOperators
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-! Quadratic forms of invariant kernels and their countable mixtures. -/
noncomputable section
namespace BreakingResonance
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

variable {S : Type*} [MeasurableSpace S]

/-- Mass of an individual step count, as a real number. -/
def countLawWeight (w : Measure ℕ) (j : ℕ) : ℝ := (w {j}).toReal

theorem countLawWeight_nonneg (w : Measure ℕ) (j : ℕ) : 0 ≤ countLawWeight w j :=
  ENNReal.toReal_nonneg

theorem countLaw_tsum (w : Measure ℕ) [IsProbabilityMeasure w] :
    (∑' j : ℕ, w {j}) = 1 := by
  simpa using (lintegral_countable' (μ := w) (fun _ => (1 : ℝ≥0∞))).symm

theorem countLawWeight_summable (w : Measure ℕ) [IsProbabilityMeasure w] :
    Summable (countLawWeight w) :=
  ENNReal.summable_toReal (by rw [countLaw_tsum]; exact ENNReal.one_ne_top)

theorem countLawWeight_tsum (w : Measure ℕ) [IsProbabilityMeasure w] :
    (∑' j, countLawWeight w j) = 1 := by
  unfold countLawWeight
  calc
    (∑' j : ℕ, (w {j}).toReal) = (∑' j : ℕ, w {j}).toReal :=
      (ENNReal.tsum_toReal_eq (f := fun j : ℕ => w {j}) (fun j => measure_ne_top w {j})).symm
    _ = 1 := by rw [countLaw_tsum]; exact ENNReal.toReal_one

/-- The quadratic form computed from the joint law of two consecutive positions. -/
def kernelQuadratic (π : Measure S) (P : Kernel S S) (f : S → ℝ) : ℝ :=
  ∫ z : S × S, f z.1 * f z.2 ∂(π ⊗ₘ P)

theorem compProd_integrable_quadratic (π : Measure S) [IsProbabilityMeasure π]
    (P : Kernel S S) [IsMarkovKernel P] (hP : P.Invariant π)
    (f : S → ℝ) (hf : MemLp f 2 π) :
    Integrable (fun z : S × S => f z.1 * f z.2) (π ⊗ₘ P) := by
  have hfst : MeasurePreserving Prod.fst (π ⊗ₘ P) π :=
    ⟨measurable_fst, Measure.fst_compProd π P⟩
  have hsnd : MeasurePreserving Prod.snd (π ⊗ₘ P) π := by
    refine ⟨measurable_snd, ?_⟩
    change (π ⊗ₘ P).snd = π
    rw [Measure.snd_compProd]
    exact hP
  exact (hf.comp_measurePreserving hfst).integrable_mul (hf.comp_measurePreserving hsnd)

theorem kernelQuadratic_congr (π : Measure S) [IsProbabilityMeasure π]
    (P : Kernel S S) [IsMarkovKernel P] (hP : P.Invariant π)
    {f g : S → ℝ} (hfg : f =ᵐ[π] g) :
    kernelQuadratic π P f = kernelQuadratic π P g := by
  have hfst : MeasurePreserving Prod.fst (π ⊗ₘ P) π :=
    ⟨measurable_fst, Measure.fst_compProd π P⟩
  have hsnd : MeasurePreserving Prod.snd (π ⊗ₘ P) π := by
    refine ⟨measurable_snd, ?_⟩
    change (π ⊗ₘ P).snd = π
    rw [Measure.snd_compProd]
    exact hP
  apply integral_congr_ae
  filter_upwards [hfst.quasiMeasurePreserving.ae_eq_comp hfg,
    hsnd.quasiMeasurePreserving.ae_eq_comp hfg] with z hx hy
  exact congrArg₂ (· * ·) hx hy

theorem kernelQuadratic_eq_iterated_integral (π : Measure S) [IsProbabilityMeasure π]
    (P : Kernel S S) [IsMarkovKernel P] (hP : P.Invariant π)
    (f : S → ℝ) (hf : MemLp f 2 π) :
    kernelQuadratic π P f = ∫ x, f x * (∫ y, f y ∂P x) ∂π := by
  rw [kernelQuadratic, Measure.integral_compProd (compProd_integrable_quadratic π P hP f hf)]
  simp_rw [integral_const_mul]

theorem compProd_eq_countable_mixture (π : Measure S) [IsProbabilityMeasure π]
    (P : Kernel S S) [IsMarkovKernel P] (K : ℕ → Kernel S S)
    [∀ j, IsMarkovKernel (K j)] (w : Measure ℕ) [IsProbabilityMeasure w]
    (hmix : ∀ x A, MeasurableSet A → P x A = ∫⁻ j, K j x A ∂w) :
    π ⊗ₘ P = Measure.sum (fun j : ℕ => w {j} • (π ⊗ₘ K j)) := by
  apply Measure.ext_prod
  intro A B hA hB
  rw [Measure.compProd_apply_prod hA hB, Measure.sum_apply _ (hA.prod hB)]
  simp_rw [hmix _ B hB, lintegral_countable']
  rw [lintegral_tsum]
  · apply tsum_congr
    intro j
    simp only [Measure.smul_apply, smul_eq_mul, Measure.compProd_apply_prod hA hB]
    rw [lintegral_mul_const _ ((K j).measurable_coe hB), mul_comm]
  · intro j
    exact (((K j).measurable_coe hB).mul_const _).aemeasurable

theorem kernelQuadratic_countable_mixture (π : Measure S) [IsProbabilityMeasure π]
    (P : Kernel S S) [IsMarkovKernel P] (hP : P.Invariant π) (K : ℕ → Kernel S S)
    [∀ j, IsMarkovKernel (K j)] (w : Measure ℕ) [IsProbabilityMeasure w]
    (hmix : ∀ x A, MeasurableSet A → P x A = ∫⁻ j, K j x A ∂w)
    (f : S → ℝ) (hf : MemLp f 2 π) :
    HasSum (fun j => countLawWeight w j * kernelQuadratic π (K j) f)
      (kernelQuadratic π P f) := by
  have hm := compProd_eq_countable_mixture π P K w hmix
  have hi := compProd_integrable_quadratic π P hP f hf
  rw [hm] at hi
  simpa only [kernelQuadratic, hm, integral_smul_measure, smul_eq_mul, countLawWeight] using
    hasSum_integral_measure hi

theorem countLaw_cosineSeries_eq_re_characteristic (w : Measure ℕ) [IsProbabilityMeasure w]
    (θ : ℝ) :
    cosineSeries (countLawWeight w) θ =
      (∫ j : ℕ, Complex.exp (((j : ℝ) * θ : ℝ) * Complex.I) ∂w).re := by
  let F (j : ℕ) := Complex.exp (((j : ℝ) * θ : ℝ) * Complex.I)
  have hF : Integrable F w := by
    apply Integrable.of_bound (Measurable.aestronglyMeasurable (measurable_of_countable F)) 1
    filter_upwards with j
    exact (Complex.norm_exp_ofReal_mul_I _).le
  change cosineSeries (countLawWeight w) θ = RCLike.re (∫ j, F j ∂w)
  rw [← integral_re hF, integral_countable hF.re]
  apply tsum_congr
  intro j
  change _ = (w {j}).toReal * (F j).re
  rw [Complex.exp_ofReal_mul_I_re]
  rfl

end BreakingResonance

#print axioms BreakingResonance.kernelQuadratic_countable_mixture
#print axioms BreakingResonance.kernelQuadratic_congr
#print axioms BreakingResonance.countLaw_cosineSeries_eq_re_characteristic
