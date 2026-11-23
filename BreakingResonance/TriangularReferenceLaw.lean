import BreakingResonance.RoundedFourierLaw
import BreakingResonance.FourierTrig
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! The triangular duration law and the Fourier estimate for its rounded counts. -/
noncomputable section
namespace BreakingResonance
open MeasureTheory Set
open scoped ENNReal

/-- The decreasing triangular density on the reference interval. The endpoint
has zero mass, so the half-open support yields the same law as the closed interval. -/
def triangularDurationLaw (T : ℝ) : Measure ℝ :=
  (volume.restrict (Ico 0 T)).withDensity (fun τ => ENNReal.ofReal (2*(T-τ)/T^2))

theorem triangularDuration_interval {T a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T) :
    triangularDurationLaw T (Ico a b) =
      ENNReal.ofReal (((T-a)^2 - (T-b)^2)/T^2) := by
  let f (τ : ℝ) := 2*(T-τ)/T^2
  have hsub : Ico a b ⊆ Ico 0 T := fun _ h => ⟨ha.trans h.1, h.2.trans_le hb⟩
  have hmeasure : (volume.restrict (Ico 0 T)).restrict (Ico a b) = volume.restrict (Ico a b) := by
    rw [Measure.restrict_restrict measurableSet_Ico, inter_eq_left.mpr hsub]
  change ((volume.restrict (Ico 0 T)).withDensity (fun t => ENNReal.ofReal (f t))) (Ico a b) = _
  rw [withDensity_apply _ measurableSet_Ico, hmeasure]
  have hi : IntegrableOn f (Ico a b) volume :=
    (intervalIntegrable_iff_integrableOn_Ico_of_le hab).mp
      ((show Continuous f by dsimp [f]; fun_prop).intervalIntegrable a b)
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ico a b)] f :=
    (ae_restrict_mem measurableSet_Ico).mono fun t ht => by
      exact div_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr (ht.2.le.trans hb))) (sq_nonneg _)
  rw [← ofReal_integral_eq_lintegral_ofReal hi hnonneg, integral_Ico_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hab]
  congr 1
  simp only [f]
  have hlin : IntervalIntegrable (fun t : ℝ => t) volume a b :=
    continuous_id.intervalIntegrable _ _
  rw [intervalIntegral.integral_div, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub intervalIntegrable_const hlin,
    intervalIntegral.integral_const, integral_id, smul_eq_mul]
  congr 1
  ring

theorem triangularDuration_probability {T : ℝ} (hT : 0 < T) :
    IsProbabilityMeasure (triangularDurationLaw T) where
  measure_univ := by
    have he : triangularDurationLaw T univ = triangularDurationLaw T (Ico 0 T) := by
      unfold triangularDurationLaw
      rw [withDensity_apply _ MeasurableSet.univ, withDensity_apply _ measurableSet_Ico,
        Measure.restrict_univ, Measure.restrict_restrict measurableSet_Ico, inter_self]
    rw [he, triangularDuration_interval le_rfl hT.le le_rfl]
    simp [hT.ne']

theorem triangularDuration_ae {T : ℝ} :
    ∀ᵐ τ ∂triangularDurationLaw T, 0 ≤ τ ∧ τ < T :=
  (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Ico)

/-- The reference count law q is obtained by the same rounding rule as the sampler. -/
def triangularCountLaw (h : ℝ) (N : ℕ) : Measure ℕ :=
  roundedDurationLaw h (triangularDurationLaw ((N : ℝ)*h))

theorem triangularCount_probability {h : ℝ} (hh : 0 < h) {N : ℕ} (hN : 0 < N) :
    IsProbabilityMeasure (triangularCountLaw h N) := by
  let : IsProbabilityMeasure (triangularDurationLaw ((N : ℝ)*h)) :=
    triangularDuration_probability (mul_pos (Nat.cast_pos.mpr hN) hh)
  unfold triangularCountLaw
  infer_instance

theorem triangularCount_ae_le {h : ℝ} (hh : 0 < h) (N : ℕ) :
    ∀ᵐ j ∂triangularCountLaw h N, j ≤ N := by
  let ρ := triangularDurationLaw ((N : ℝ)*h)
  have hfloor : ∀ᵐ τ ∂ρ, Nat.floor (τ/h) < N :=
    (triangularDuration_ae (T := (N : ℝ)*h)).mono fun τ hτ =>
      (Nat.floor_lt (div_nonneg hτ.1 hh.le)).mpr ((div_lt_iff₀ hh).mpr hτ.2)
  have hs : MeasurableSet {j : ℕ | j ≤ N} := Set.Countable.measurableSet (Set.to_countable _)
  unfold triangularCountLaw roundedDurationLaw
  refine ae_add_measure_iff.mpr ⟨?_, ?_⟩
  · exact Measure.ae_smul_measure
      ((ae_map_iff (measurable_floorDuration h).aemeasurable hs).mpr
        (hfloor.mono fun _ ht => ht.le)) _
  · exact Measure.ae_smul_measure
      ((ae_map_iff (measurable_succFloorDuration h).aemeasurable hs).mpr
        (hfloor.mono fun _ ht => ht)) _

/-- The one-sided comparison bound follows from the largest possible count. -/
theorem cosineSeries_gap_upper_of_count_le (q : Measure ℕ) [IsProbabilityMeasure q]
    (N : ℕ) (hN : ∀ᵐ j ∂q, j ≤ N) (θ : ℝ) :
    1 - cosineSeries (countLawWeight q) θ ≤ min ((N : ℝ)^2*θ^2/2) 2 := by
  let f (j : ℕ) := Real.cos ((j : ℝ)*θ)
  have hi : Integrable f q := Integrable.of_bound (measurable_of_countable f).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun _ => Real.abs_cos_le_one _)
  have he : 1 - cosineSeries (countLawWeight q) θ = ∫ j, 1 - f j ∂q := by
    rw [countLaw_cosineSeries_eq_integral_cos, integral_sub (integrable_const _) hi]
    simp only [integral_const, probReal_univ, one_smul]
    rfl
  rw [he]
  have him : Integrable (fun j => 1 - f j) q := (integrable_const (1 : ℝ)).sub hi
  refine le_min ?_ ?_
  · have hb := integral_mono_ae him (integrable_const ((N : ℝ)^2*θ^2/2)) (by
      filter_upwards [hN] with j hj
      change 1 - Real.cos ((j : ℝ)*θ) ≤ (N : ℝ)^2*θ^2/2
      have hj₂ : (j : ℝ)^2 ≤ (N : ℝ)^2 :=
        (sq_le_sq₀ (Nat.cast_nonneg _) (Nat.cast_nonneg _)).mpr (Nat.cast_le.mpr hj)
      calc
        _ ≤ ((j : ℝ)*θ)^2/2 := one_sub_cos_le_sq_div_two _
        _ ≤ _ := by
          rw [mul_pow]
          exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hj₂ (sq_nonneg _)) (by norm_num))
    simpa only [integral_const, probReal_univ, one_smul] using hb
  · have hb := integral_mono him (integrable_const (2 : ℝ)) fun j => by
      change 1 - Real.cos ((j : ℝ)*θ) ≤ 2
      linarith only [Real.neg_one_le_cos ((j : ℝ)*θ)]
    simpa only [integral_const, probReal_univ, one_smul] using hb

end BreakingResonance

#print axioms BreakingResonance.triangularDuration_interval
#print axioms BreakingResonance.triangularCount_ae_le
#print axioms BreakingResonance.cosineSeries_gap_upper_of_count_le
