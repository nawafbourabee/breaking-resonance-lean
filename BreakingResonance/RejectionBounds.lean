import PersistencePays.KernelEntropy
import Mathlib

/-! A probability-kernel version of the first-acceptance argument in
Theorem 2. The small acceptance estimate is an explicit hypothesis here;
the expanding-orbit construction proving that estimate is not assumed to
have been formalized. -/
namespace BreakingResonance
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory
variable {S : Type*} [MeasurableSpace S]

def totalVariation (μ ν : Measure S) : ℝ≥0∞ :=
  ⨆ A : Set S, ⨆ (_ : MeasurableSet A), ENNReal.ofReal |μ.real A - ν.real A|

theorem event_le_totalVariation (μ ν : Measure S) (A : Set S)
    (hA : MeasurableSet A) :
    ENNReal.ofReal (μ.real A - ν.real A) ≤ totalVariation μ ν := by
  exact (ENNReal.ofReal_le_ofReal (le_abs_self _)).trans
    (le_iSup₂_of_le A hA le_rfl)

theorem retained_mass (K : Kernel S S) (μ : Measure S)
    (E : Set S) (hE : MeasurableSet E) (c : ℝ≥0∞)
    (hstay : ∀ x ∈ E, c ≤ K x E) :
    c * μ E ≤ (K ∘ₘ μ) E := by
  rw [Measure.bind_apply hE K.aemeasurable]
  calc
    c * μ E = ∫⁻ _ in E, c ∂μ := by simp
    _ ≤ ∫⁻ x in E, K x E ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hE] with x hx
      exact hstay x hx
    _ ≤ ∫⁻ x, K x E ∂μ := lintegral_mono' Measure.restrict_le_self le_rfl

theorem retained_mass_real (K : Kernel S S) [IsMarkovKernel K]
    (μ : Measure S) [IsProbabilityMeasure μ]
    (E : Set S) (hE : MeasurableSet E) (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hstay : ∀ x ∈ E, ENNReal.ofReal (1-a) ≤ K x E) :
    μ.real E - a ≤ (K ∘ₘ μ).real E := by
  have h := retained_mass K μ E hE (ENNReal.ofReal (1-a)) hstay
  have ht := ENNReal.toReal_mono (measure_ne_top (K ∘ₘ μ) E) h
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith)] at ht
  have hμ : μ.real E ≤ 1 := by exact measureReal_le_one
  have hm := mul_le_mul_of_nonneg_left hμ ha
  change (1-a) * μ.real E ≤ (K ∘ₘ μ).real E at ht
  nlinarith

theorem retained_mass_iterates (K : Kernel S S) [IsMarkovKernel K]
    (μ : Measure S) [IsProbabilityMeasure μ]
    (E : Set S) (hE : MeasurableSet E) (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hstay : ∀ x ∈ E, ENNReal.ofReal (1-a) ≤ K x E) (n : ℕ) :
    μ.real E - (n : ℝ) * a ≤ (PersistencePays.evolve (fun _ => K) μ n).real E := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := retained_mass_real K (PersistencePays.evolve (fun _ => K) μ n)
      E hE a ha ha1 hstay
    simp only [PersistencePays.evolve_succ]
    push_cast
    linarith

theorem rejection_totalVariation_lower (K : Kernel S S) [IsMarkovKernel K]
    (μ π : Measure S) [IsProbabilityMeasure μ] [IsProbabilityMeasure π]
    (A E : Set S) (hA : MeasurableSet A) (hE : MeasurableSet E) (hEA : E ⊆ A)
    (hπ : π.real A = 1 / 2) (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hstart : 1-b ≤ μ.real E)
    (hstay : ∀ x ∈ E, ENNReal.ofReal (1-a) ≤ K x E) (n : ℕ) :
    ENNReal.ofReal (1/2-b-(n : ℝ)*a) ≤
      totalVariation (PersistencePays.evolve (fun _ => K) μ n) π := by
  have hr := retained_mass_iterates K μ E hE a ha ha1 hstay n
  have hmono := measureReal_mono (μ := PersistencePays.evolve (fun _ => K) μ n)
    hEA (by finiteness)
  apply (ENNReal.ofReal_le_ofReal ?_).trans
    (event_le_totalVariation (PersistencePays.evolve (fun _ => K) μ n) π A hA)
  rw [hπ]
  linarith

theorem attempts_lower_from_rejection (K : Kernel S S) [IsMarkovKernel K]
    (μ π : Measure S) [IsProbabilityMeasure μ] [IsProbabilityMeasure π]
    (A E : Set S) (hA : MeasurableSet A) (hE : MeasurableSet E) (hEA : E ⊆ A)
    (hπ : π.real A = 1 / 2) (a b : ℝ) (ha : 0 < a) (ha1 : a ≤ 1)
    (hb : b ≤ 1/20) (hstart : 1-b ≤ μ.real E)
    (hstay : ∀ x ∈ E, ENNReal.ofReal (1-a) ≤ K x E) (n : ℕ)
    (htv : totalVariation (PersistencePays.evolve (fun _ => K) μ n) π ≤ 1/4) :
    1/(5*a) ≤ (n : ℝ) := by
  have hl := (rejection_totalVariation_lower K μ π A E hA hE hEA hπ a b
    ha.le ha1 hstart hstay n).trans htv
  have hreal : 1/2-b-(n : ℝ)*a ≤ 1/4 := by
    have ht := ENNReal.toReal_mono (by norm_num : (1/4 : ℝ≥0∞) ≠ ∞) hl
    by_cases hnonneg : 0 ≤ 1/2-b-(n : ℝ)*a
    · rw [ENNReal.toReal_ofReal hnonneg] at ht
      norm_num at ht
      linarith
    · linarith
  apply (div_le_iff₀ (by positivity : 0 < 5*a)).mpr
  nlinarith

end
end BreakingResonance
