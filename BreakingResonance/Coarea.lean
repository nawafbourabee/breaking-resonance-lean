import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BreakingResonance

variable {S : Type*} [MeasurableSpace S]

/-- Integrating the flow through strict upper level sets gives the integral
of the positive part of the difference. -/
theorem lintegral_crossing_level_sets
    (ν : Measure (S × S)) [IsFiniteMeasure ν] {g : S → ℝ} (hg : Measurable g)
    {C : ℝ} (hlo : ∀ x, 0 ≤ g x) (hhi : ∀ x, g x ≤ C) :
    (∫⁻ t in Ioc 0 C, ν ({x | t < g x} ×ˢ {x | t < g x}ᶜ)) =
      ∫⁻ z : S × S, ENNReal.ofReal (g z.1-g z.2) ∂ν := by
  let H : Set (ℝ × (S×S)) := {z | g z.2.2 ≤ z.1 ∧ z.1 < g z.2.1}
  have hH : MeasurableSet H :=
    (measurableSet_le (hg.comp (measurable_snd.comp measurable_snd)) measurable_fst).inter
      (measurableSet_lt measurable_fst (hg.comp (measurable_fst.comp measurable_snd)))
  let F := H.indicator (fun _ => (1 : ℝ≥0∞))
  have hF : Measurable F := measurable_const.indicator hH
  let μ := (volume : Measure ℝ).restrict (Ioc 0 C)
  have hr (t : ℝ) : (∫⁻ z : S×S, F (t,z) ∂ν) =
      ν ({x | t < g x} ×ˢ {x | t < g x}ᶜ) := by
    have hm : MeasurableSet ({x | t < g x} ×ˢ {x | t < g x}ᶜ) :=
      (measurableSet_lt measurable_const hg).prod (measurableSet_lt measurable_const hg).compl
    have he : (fun z : S×S => F (t,z)) =
        ({x | t < g x} ×ˢ {x | t < g x}ᶜ).indicator (fun _ => (1:ℝ≥0∞)) := by
      funext z
      have heq : (t,z) ∈ H ↔ z ∈ {x | t < g x} ×ˢ {x | t < g x}ᶜ := by
        simp [H, not_lt, and_comm]
      by_cases h : (t,z) ∈ H
      · simp [F, h, heq.mp h]
      · simp [F, h, mt heq.mpr h]
    rw [he, lintegral_indicator_const hm]
    simp
  have hl (z : S×S) : (∫⁻ t, F (t,z) ∂μ) = ENNReal.ofReal (g z.1-g z.2) := by
    have he : (fun t : ℝ => F (t,z)) = (Ico (g z.2) (g z.1)).indicator
        (fun _ => (1:ℝ≥0∞)) := by
      funext t
      rfl
    rw [he,lintegral_indicator_const measurableSet_Ico,one_mul]
    change ((volume : Measure ℝ).restrict (Ioc 0 C)) (Ico (g z.2) (g z.1)) = _
    rw [Measure.restrict_apply measurableSet_Ico]
    apply le_antisymm
    · rw [← Real.volume_Ico]
      exact measure_mono inter_subset_left
    · rw [← Real.volume_Ioo]
      exact measure_mono (fun _ ht => ⟨⟨ht.1.le,ht.2⟩,
        ⟨(hlo z.2).trans_lt ht.1,ht.2.le.trans (hhi z.1)⟩⟩)
  calc
    _ = ∫⁻ t, ∫⁻ z, F (t,z) ∂ν ∂μ := lintegral_congr fun t => (hr t).symm
    _ = ∫⁻ z, ∫⁻ t, F (t,z) ∂μ ∂ν := by
      rw [← lintegral_prod F hF.aemeasurable, lintegral_prod_symm F hF.aemeasurable]
    _ = _ := lintegral_congr hl

end BreakingResonance

#print axioms BreakingResonance.lintegral_crossing_level_sets
