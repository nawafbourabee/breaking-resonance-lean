import BreakingResonance.Coarea
import BreakingResonance.MarkovL2

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace BreakingResonance

variable {S : Type*} [MeasurableSpace S]

/-- Restricted conductance in stationary flow notation. -/
def RestrictedConductance (π : Measure S) (P : Kernel S S) (s φ : ℝ) : Prop :=
  ∀ A : Set S, MeasurableSet A → ENNReal.ofReal s ≤ π A → π A ≤ 1/2 →
    ENNReal.ofReal φ * π A ≤ (π ⊗ₘ P) (A ×ˢ Aᶜ)

/-- Integrate the restricted conductance estimate over levels of a bounded
nonnegative function supported on a set of mass at most one half. -/
theorem restrictedConductance_crossing_bound
    (π : Measure S) [IsProbabilityMeasure π] (P : Kernel S S) [IsMarkovKernel P]
    {s φ C : ℝ} (hcond : RestrictedConductance π P s φ) (_hC : 0 ≤ C)
    {g : S → ℝ} (hg : Measurable g) (hlo : ∀ x, 0 ≤ g x) (hhi : ∀ x, g x ≤ C)
    (hsupport : π {x | 0 < g x} ≤ 1/2) :
    ENNReal.ofReal φ * (∫⁻ x, ENNReal.ofReal (g x) ∂π) ≤
      ENNReal.ofReal φ * ENNReal.ofReal s * ENNReal.ofReal C +
        ∫⁻ z : S×S, ENNReal.ofReal (g z.1-g z.2) ∂(π ⊗ₘ P) := by
  let A (t : ℝ) : Set S := {x | t < g x}
  let ν := π ⊗ₘ P
  let μ := (volume : Measure ℝ).restrict (Ioc 0 C)
  have hm : Measurable (fun t => π (A t)) :=
    Antitone.measurable fun _ _ h => measure_mono fun _ hx => h.trans_lt hx
  have hA (t : ℝ) : MeasurableSet (A t) := measurableSet_lt measurable_const hg
  have ht : (∫⁻ x, ENNReal.ofReal (g x) ∂π) = ∫⁻ t, π (A t) ∂μ := by
    rw [lintegral_eq_lintegral_meas_lt π (Filter.Eventually.of_forall hlo) hg.aemeasurable]
    change (∫⁻ t in Ioi 0, π (A t)) = ∫⁻ t, π (A t) ∂μ
    calc
      _ = ∫⁻ t in Ioi 0, (Ioc 0 C).indicator (fun t => π (A t)) t := by
        apply setLIntegral_congr_fun measurableSet_Ioi
        intro t ht
        by_cases h : t ≤ C
        · exact (indicator_of_mem (show t ∈ Ioc 0 C from ⟨ht,h⟩) (fun t => π (A t))).symm
        · have hz : A t = ∅ := by
            ext x
            simp [A, not_lt.mpr ((hhi x).trans (le_of_not_ge h))]
          rw [indicator_of_notMem (show t ∉ Ioc 0 C from fun hmem => h hmem.2)]
          change π (A t) = 0
          rw [hz,measure_empty]
      _ = _ := by
        rw [lintegral_indicator measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc]
        rw [inter_eq_left.mpr (fun _ hx => hx.1)]
  have hpt (t : ℝ) (ht : t ∈ Ioc 0 C) :
      ENNReal.ofReal φ * π (A t) ≤
        ENNReal.ofReal φ * ENNReal.ofReal s + ν (A t ×ˢ (A t)ᶜ) := by
    by_cases h : ENNReal.ofReal s ≤ π (A t)
    · have hf := hcond (A t) (hA t) h
        ((measure_mono (fun _ hx => ht.1.trans hx)).trans hsupport)
      exact hf.trans le_add_self
    · calc
        ENNReal.ofReal φ * π (A t) ≤ ENNReal.ofReal φ * ENNReal.ofReal s :=
          mul_le_mul' le_rfl (le_of_not_ge h)
        _ ≤ _ := le_self_add
  have ha := lintegral_mono_ae (μ := μ) (by
    filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ioc] with t ht
    exact hpt t ht)
  have hf := lintegral_crossing_level_sets ν hg hlo hhi
  change (∫⁻ t, ν (A t ×ˢ (A t)ᶜ) ∂μ) = _ at hf
  rw [ht,← lintegral_const_mul _ hm]
  refine ha.trans_eq ?_
  rw [lintegral_add_left measurable_const,lintegral_const,hf]
  have hμ : μ univ = ENNReal.ofReal C := by
    simp [μ, Real.volume_Ioc]
  rw [hμ]

end BreakingResonance

#print axioms BreakingResonance.RestrictedConductance
#print axioms BreakingResonance.restrictedConductance_crossing_bound
