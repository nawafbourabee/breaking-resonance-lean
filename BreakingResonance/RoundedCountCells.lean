import BreakingResonance.TriangularReferenceLaw
import BreakingResonance.ProposalEntropy

/-! Rounding a duration law on the reference interval, cell by cell. -/
noncomputable section
namespace BreakingResonance
open MeasureTheory Set
open scoped ENNReal

theorem floorDuration_map_apply_singleton {ρ : Measure ℝ}
    (h : ℝ) (hh : 0 < h) (hpos : ∀ᵐ τ ∂ρ, 0 ≤ τ) (j : ℕ) :
    ρ.map (fun τ => Nat.floor (τ/h)) {j} =
      ρ (Ico ((j : ℝ)*h) (((j : ℝ)+1)*h)) := by
  rw [Measure.map_apply (measurable_floorDuration h) (measurableSet_singleton j)]
  apply measure_congr
  filter_upwards [hpos] with τ hτ
  change (Nat.floor (τ/h) = j) = (((j : ℝ)*h ≤ τ) ∧ (τ < ((j : ℝ)+1)*h))
  rw [Nat.floor_eq_iff (div_nonneg hτ hh.le), le_div_iff₀ hh, div_lt_iff₀ hh]

/-- Unrounded cell masses give the law of the integer part of τ/h. -/
theorem floorDuration_map_eq_cell_sum (h : ℝ) (hh : 0 < h) (N : ℕ) (ρ : Measure ℝ)
    (hs : ∀ᵐ τ ∂ρ, 0 ≤ τ ∧ τ < (N : ℝ)*h) :
    ρ.map (fun τ => Nat.floor (τ/h)) =
      ∑ j ∈ Finset.range N, ρ (Ico ((j : ℝ)*h) (((j : ℝ)+1)*h)) • Measure.dirac j := by
  apply Measure.ext_of_singleton
  intro k
  rw [Measure.finsetSum_apply, floorDuration_map_apply_singleton h hh
    (hs.mono fun _ hτ => hτ.1)]
  simp only [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ (measurableSet_singleton k),
    indicator_singleton, Pi.one_apply]
  by_cases hk : k < N
  · rw [Finset.sum_eq_single k]
    · simp
    · intro j _ hj
      simp [hj]
    · exact fun h => (h (Finset.mem_range.mpr hk)).elim
  · have hz : ρ (Ico ((k : ℝ)*h) (((k : ℝ)+1)*h)) = 0 := by
      have hdis : Ico ((k : ℝ)*h) (((k : ℝ)+1)*h) =ᵐ[ρ] (∅ : Set ℝ) := by
        filter_upwards [hs] with τ hτ
        change ((k : ℝ)*h ≤ τ ∧ τ < ((k : ℝ)+1)*h) = False
        apply propext
        rw [iff_false]
        intro hcell
        have hle : (N : ℝ)*h ≤ (k : ℝ)*h :=
          mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (le_of_not_gt hk)) hh.le
        exact (not_lt_of_ge (hle.trans hcell.1)) hτ.2
      rw [measure_congr hdis, measure_empty]
    rw [hz]
    symm
    apply Finset.sum_eq_zero
    intro j hj
    have hne : j ≠ k := fun he => hk (he ▸ Finset.mem_range.mp hj)
    simp [hne]

theorem roundedDuration_eq_cell_sum (h : ℝ) (hh : 0 < h) (N : ℕ) (ρ : Measure ℝ)
    (hs : ∀ᵐ τ ∂ρ, 0 ≤ τ ∧ τ < (N : ℝ)*h) :
    roundedDurationLaw h ρ =
      ∑ j ∈ Finset.range N, ∑ b ∈ Finset.range 2,
        ((1/2 : ℝ≥0∞) * ρ (Ico ((j : ℝ)*h) (((j : ℝ)+1)*h))) • Measure.dirac (j+b) := by
  have hm : Measurable (fun n : ℕ => n+1) := measurable_of_countable _
  have he : ρ.map (fun τ => Nat.floor (τ/h)+1) =
      (ρ.map (fun τ => Nat.floor (τ/h))).map (fun n : ℕ => n+1) :=
    (Measure.map_map hm (measurable_floorDuration h)).symm
  rw [roundedDurationLaw, he, floorDuration_map_eq_cell_sum h hh N ρ hs]
  rw [Measure.map_finset_sum hm.aemeasurable]
  simp only [Measure.map_smul, Measure.map_dirac' hm, Finset.smul_sum, smul_smul]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.add_zero]

theorem triangularDuration_cellMass {h : ℝ} (hh : 0 < h) {N j : ℕ} (hj : j < N) :
    triangularDurationLaw ((N : ℝ)*h) (Ico ((j : ℝ)*h) (((j : ℝ)+1)*h)) =
      ENNReal.ofReal (2 * triangularWeight h N j / ((N : ℝ)*h)^2) := by
  have hj' : (j : ℝ)+1 ≤ N := by exact_mod_cast hj
  rw [triangularDuration_interval (mul_nonneg (Nat.cast_nonneg _) hh.le)
    (mul_le_mul_of_nonneg_right (by linarith) hh.le) (mul_le_mul_of_nonneg_right hj' hh.le)]
  congr 1
  congr 1
  unfold triangularWeight
  ring

/-- The rounded triangular count law in Lemma 5.3 is exactly the endpoint
mixture used for Proposition 6.8, specialized to Dirac laws. -/
theorem triangularCount_eq_endpointLaw {h : ℝ} (hh : 0 < h) (N : ℕ) :
    triangularCountLaw h N =
      triangularEndpointLaw (fun j : ℕ => ⟨Measure.dirac j, inferInstance⟩) h N := by
  unfold triangularCountLaw triangularEndpointLaw
  rw [roundedDuration_eq_cell_sum h hh N _ triangularDuration_ae,
    Finset.product_eq_sprod, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro j hj
  rw [triangularDuration_cellMass hh (Finset.mem_range.mp hj)]
  have hhalfmass : (1/2 : ℝ≥0∞) *
       ENNReal.ofReal (2 * triangularWeight h N j / ((N : ℝ)*h)^2) =
       ENNReal.ofReal (triangularWeight h N j / ((N : ℝ)*h)^2) := by
    rw [show (1/2 : ℝ≥0∞) = ENNReal.ofReal (1/2 : ℝ) by
          rw [ENNReal.ofReal_div_of_pos (by norm_num)]; norm_num,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1/2)]
    congr 1
    ring
  rw [hhalfmass]
  rfl

end BreakingResonance

#print axioms BreakingResonance.roundedDuration_eq_cell_sum
#print axioms BreakingResonance.triangularCount_eq_endpointLaw
