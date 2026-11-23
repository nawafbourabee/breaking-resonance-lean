import BreakingResonance.MarkovL2
import PersistencePays.KernelEntropy

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory ENNReal

namespace BreakingResonance

variable {S : Type*} [MeasurableSpace S]

/-- Detailed balance identifies the new density with integration of the old
density against the transition kernel. -/
theorem reversible_bind_withDensity
    (π : Measure S) [IsProbabilityMeasure π] (P : Kernel S S) [IsMarkovKernel P]
    (hrev : P.IsReversible π) {f : S → ℝ≥0∞} (hf : Measurable f) :
    P ∘ₘ π.withDensity f = π.withDensity (fun x => ∫⁻ y, f y ∂P x) := by
  ext A hA
  rw [Measure.bind_apply hA P.aemeasurable, lintegral_withDensity_eq_lintegral_mul _ hf
    (P.measurable_coe hA), withDensity_apply _ hA]
  let F (z : S×S) := f z.1 * A.indicator (fun _ => (1:ℝ≥0∞)) z.2
  have hF : Measurable F := (hf.comp measurable_fst).mul
    ((measurable_const.indicator hA).comp measurable_snd)
  have hFs : Measurable (F ∘ Prod.swap) := hF.comp measurable_swap
  have hs (x : S) : (∫⁻ y, F (x,y) ∂P x) = f x*P x A := by
    change (∫⁻ y, f x * A.indicator (fun _ => (1:ℝ≥0∞)) y ∂P x) = _
    rw [lintegral_const_mul _ (measurable_const.indicator hA),
      lintegral_indicator_const hA, one_mul]
  have ht (x : S) : (∫⁻ y, F (y,x) ∂P x) = A.indicator
      (fun z => ∫⁻ y, f y ∂P z) x := by
    by_cases hx : x ∈ A
    · simp [F,hx]
    · simp [F,hx]
  calc
    _ = ∫⁻ z, F z ∂(π ⊗ₘ P) := by
      rw [Measure.lintegral_compProd hF]
      exact lintegral_congr (fun x => (hs x).symm)
    _ = ∫⁻ z, F z ∂((π ⊗ₘ P).map Prod.swap) := by
      rw [reversible_compProd_map_swap π P hrev]
    _ = ∫⁻ z, F (Prod.swap z) ∂(π ⊗ₘ P) := lintegral_map hF measurable_swap
    _ = _ := by
      rw [← lintegral_indicator hA]
      rw [show (fun z => F (Prod.swap z)) = F ∘ Prod.swap from rfl,
        Measure.lintegral_compProd hFs]
      exact lintegral_congr ht

theorem markovAction_integrable_bound {π : Measure S} [IsFiniteMeasure π]
    {f : S → ℝ} (hf : Measurable f) {C : ℝ}
    (h0 : ∀ x, 0 ≤ f x) (hC : ∀ x, f x ≤ C) : Integrable f π :=
  (memLp_of_bounded (Filter.Eventually.of_forall fun x => ⟨h0 x,hC x⟩)
    hf.aestronglyMeasurable 1).integrable le_rfl

theorem markovAction_measurable_bounded (P : Kernel S S) [IsMarkovKernel P]
    {f : S → ℝ} (hf : Measurable f) {C : ℝ}
    (h0 : ∀ x, 0 ≤ f x) (hC : ∀ x, f x ≤ C) :
    Measurable (markovAction P f) ∧
    (∀ x, 0 ≤ markovAction P f x) ∧ (∀ x, markovAction P f x ≤ C) := by
  have he : ∀ x, markovAction P f x = (∫⁻ y, ENNReal.ofReal (f y) ∂P x).toReal :=
    fun x => integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall h0)
      hf.aestronglyMeasurable
  refine ⟨?_,fun x => integral_nonneg h0,fun x => ?_⟩
  · rw [funext he]
    exact (hf.ennreal_ofReal.lintegral_kernel (κ := P)).ennreal_toReal
  · change (∫ y, f y ∂P x) ≤ C
    simpa only [integral_const, probReal_univ, one_smul] using
      integral_mono (markovAction_integrable_bound (π := P x) hf h0 hC)
        (integrable_const C) hC

theorem reversible_bind_real_density
    (π : Measure S) [IsProbabilityMeasure π] (P : Kernel S S) [IsMarkovKernel P]
    (hrev : P.IsReversible π) {f : S → ℝ} (hf : Measurable f) {C : ℝ}
    (h0 : ∀ x, 0 ≤ f x) (hC : ∀ x, f x ≤ C) :
    P ∘ₘ π.withDensity (ENNReal.ofReal ∘ f) =
      π.withDensity (ENNReal.ofReal ∘ markovAction P f) := by
  change P ∘ₘ π.withDensity (fun x => ENNReal.ofReal (f x)) =
    π.withDensity (fun x => ENNReal.ofReal (markovAction P f x))
  rw [reversible_bind_withDensity π P hrev hf.ennreal_ofReal]
  congr 1
  funext x
  exact (ofReal_integral_eq_lintegral_ofReal
    (markovAction_integrable_bound (π := P x) hf h0 hC)
    (Filter.Eventually.of_forall h0)).symm

/-- The density after k applications of the position kernel. -/
def densityIterate (P : Kernel S S) (f : S → ℝ) : ℕ → (S → ℝ)
  | 0 => f
  | k+1 => markovAction P (densityIterate P f k)

theorem densityIterate_bounded (P : Kernel S S) [IsMarkovKernel P]
    {f : S → ℝ} (hf : Measurable f) {C : ℝ}
    (h0 : ∀ x, 0 ≤ f x) (hC : ∀ x, f x ≤ C) :
    ∀ k, Measurable (densityIterate P f k) ∧
      (∀ x, 0 ≤ densityIterate P f k x) ∧ (∀ x, densityIterate P f k x ≤ C) := by
  intro k
  induction k with
  | zero => exact ⟨hf,h0,hC⟩
  | succ k ih => exact markovAction_measurable_bounded P ih.1 ih.2.1 ih.2.2

theorem reversible_evolve_density
    (π : Measure S) [IsProbabilityMeasure π] (P : Kernel S S) [IsMarkovKernel P]
    (hrev : P.IsReversible π) {f : S → ℝ} (hf : Measurable f) {C : ℝ}
    (h0 : ∀ x, 0 ≤ f x) (hC : ∀ x, f x ≤ C) :
    ∀ k, PersistencePays.evolve (fun _ => P) (π.withDensity (ENNReal.ofReal ∘ f)) k =
      π.withDensity (ENNReal.ofReal ∘ densityIterate P f k) := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [PersistencePays.evolve_succ, ih]
    have hk := densityIterate_bounded P hf h0 hC k
    exact reversible_bind_real_density π P hrev hk.1 hk.2.1 hk.2.2

end BreakingResonance

#print axioms BreakingResonance.reversible_bind_withDensity
#print axioms BreakingResonance.reversible_evolve_density
