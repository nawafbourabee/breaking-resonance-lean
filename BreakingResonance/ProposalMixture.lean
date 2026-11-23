import PersistencePays.EntropyDual
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-! Convexity of relative entropy for the finite mixture in Proposition 6.8. -/
noncomputable section
namespace BreakingResonance
open PersistencePays MeasureTheory InformationTheory
open scoped ENNReal

variable {S I : Type*} [MeasurableSpace S]

theorem klDiv_finite_mixture_le (s : Finset I) (w : I → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hw₁ : ∑ i ∈ s, w i = 1)
    (μ : I → ProbabilityMeasure S) (π : Measure S) [IsProbabilityMeasure π]
    (hfinite : ∀ i ∈ s, klDiv (μ i : Measure S) π ≠ ∞) :
    klDiv (∑ i ∈ s, ENNReal.ofReal (w i) • (μ i : Measure S)) π ≤
      ENNReal.ofReal (∑ i ∈ s, w i * (klDiv (μ i : Measure S) π).toReal) := by
  let ν : Measure S := ∑ i ∈ s, ENNReal.ofReal (w i) • (μ i : Measure S)
  have hmass : ν Set.univ = 1 := by
    simp only [ν, Measure.finsetSum_apply, Measure.smul_apply, measure_univ,
      smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg hw, hw₁, ENNReal.ofReal_one]
  let : IsProbabilityMeasure ν := ⟨hmass⟩
  change klDiv ν π ≤ _
  apply klDiv_le_of_bounded_duals ν π
  intro f hf
  have hintegral : ∫ x, f x ∂ν = ∑ i ∈ s, w i * ∫ x, f x ∂(μ i : Measure S) := by
    dsimp only [ν]
    rw [integral_finsetSum_measure (fun i _ =>
      (hf.integrable (μ i : Measure S)).smul_measure ENNReal.ofReal_ne_top)]
    apply Finset.sum_congr rfl
    intro i hi
    rw [integral_smul_measure, ENNReal.toReal_ofReal (hw i hi), smul_eq_mul]
  have hdual : entropyDual ν π f =
      ∑ i ∈ s, w i * entropyDual (μ i : Measure S) π f := by
    unfold entropyDual
    simp only [hintegral, mul_add, mul_sub, mul_one, Finset.sum_add_distrib,
      Finset.sum_sub_distrib]
    rw [← Finset.sum_mul, hw₁, one_mul]
  rw [hdual]
  apply ENNReal.ofReal_le_ofReal
  apply Finset.sum_le_sum
  intro i hi
  apply mul_le_mul_of_nonneg_left _ (hw i hi)
  have hbound := ENNReal.toReal_mono (hfinite i hi)
    (entropyDual_le_klDiv (μ i : Measure S) π hf)
  exact (le_max_left (entropyDual (μ i : Measure S) π f) 0).trans
    (by simpa only [ENNReal.toReal_ofReal'] using hbound)

end BreakingResonance

#print axioms BreakingResonance.klDiv_finite_mixture_le
