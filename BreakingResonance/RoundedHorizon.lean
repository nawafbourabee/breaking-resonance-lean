import BreakingResonance.DurationNonresonance

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace BreakingResonance

theorem roundedDuration_ae_horizon (ρ : Measure ℝ) {h T : ℝ} (hh : 0 < h)
    (hρ : ∀ᵐ τ ∂ρ, 0 ≤ τ ∧ τ ≤ T) :
    ∀ᵐ j : ℕ ∂roundedDurationLaw h ρ, (j:ℝ)*h ≤ T+h := by
  unfold roundedDurationLaw
  rw [ae_add_measure_iff]
  have hu : MeasurableSet {j : ℕ | (j:ℝ)*h ≤ T+h} := Set.to_countable _ |>.measurableSet
  have hf : ∀ᵐ τ ∂ρ, (Nat.floor (τ/h):ℝ)*h ≤ τ := by
    filter_upwards [hρ] with τ hτ
    exact (le_div_iff₀ hh).mp (Nat.floor_le (div_nonneg hτ.1 hh.le))
  constructor
  · apply Measure.ae_smul_measure _ _
    apply (ae_map_iff (measurable_floorDuration h).aemeasurable hu).mpr
    filter_upwards [hρ,hf] with τ hτ hb
    linarith only [hh,hτ.2,hb]
  · apply Measure.ae_smul_measure _ _
    apply (ae_map_iff (measurable_succFloorDuration h).aemeasurable hu).mpr
    filter_upwards [hρ,hf] with τ hτ hb
    simp only [Nat.cast_add,Nat.cast_one,add_mul,one_mul]
    linarith only [hτ.2,hb]

theorem conditional_count_horizon {ρ : Measure ℝ} {τstar h Tstar : ℝ}
    (hh : 0 < h) (hρ : ∀ᵐ τ ∂ρ, 0 < τ) (hstar : τstar+h ≤ Tstar) :
    ∀ᵐ j : ℕ ∂roundedDurationLaw h (conditionalDurationLaw ρ τstar), (j:ℝ)*h ≤ Tstar :=
  (roundedDuration_ae_horizon (conditionalDurationLaw ρ τstar) hh
    ((conditionalDuration_positive_bounded ρ τstar hρ).mono fun _ ht => ⟨ht.1.le,ht.2⟩)).mono
      fun _ hj => hj.trans hstar

end BreakingResonance

#print axioms BreakingResonance.conditional_count_horizon
