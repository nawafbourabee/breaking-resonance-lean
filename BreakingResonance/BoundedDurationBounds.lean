import BreakingResonance.BoundedDurationFourier
import BreakingResonance.DurationNonresonance

/-! The constants for the triangular and uniform duration laws in Lemma 5.4.
The uniform law has half the duration horizon of the triangular reference law. -/
noncomputable section
namespace BreakingResonance
open MeasureTheory Set

theorem conditionalDuration_eq_of_ae_le (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    (T : ℝ) (hs : ∀ᵐ τ ∂ρ, τ ≤ T) :
    ρ (Iic T) = 1 ∧ conditionalDurationLaw ρ T = ρ := by
  have he : ρ.restrict (Iic T) = ρ := Measure.restrict_eq_self_of_ae_mem hs
  have hm : ρ (Iic T) = 1 := by
    rw [← Measure.restrict_apply_univ, he, measure_univ]
  exact ⟨hm, by rw [conditionalDurationLaw, hm, inv_one, one_smul, he]⟩

theorem cosineSeries_abs_frequency (w : ℕ → ℝ) (θ : ℝ) :
    cosineSeries w |θ| = cosineSeries w θ := by
  apply tsum_congr
  intro j
  have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
  calc
    w j * Real.cos ((j : ℝ)*|θ|) = w j * Real.cos |(j : ℝ)*θ| := by
      rw [abs_mul, abs_of_nonneg hj]
    _ = _ := by rw [Real.cos_abs]

theorem countLaw_cosine_zero (q : Measure ℕ) [IsProbabilityMeasure q] :
    cosineSeries (countLawWeight q) 0 = 1 := by
  unfold cosineSeries
  simp only [mul_zero, Real.cos_zero, mul_one]
  exact countLawWeight_tsum q

theorem roundedDuration_cosine_pi (h : ℝ) (ρ : Measure ℝ) [IsProbabilityMeasure ρ] :
    cosineSeries (countLawWeight (roundedDurationLaw h ρ)) Real.pi = 0 := by
  have hπ : |Real.pi| = Real.pi := abs_of_pos Real.pi_pos
  have h := roundedDuration_abs_cosineSeries_high h ρ (ζ := Real.pi) (θ := Real.pi)
    Real.pi_pos.le (by rw [hπ]) (by rw [hπ])
  rw [Real.cos_pi_div_two] at h
  exact abs_nonpos_iff.mp h

theorem sine_lower_quarter {x : ℝ} (hx : 0 ≤ x) : -x/4 ≤ Real.sin x := by
  by_cases hπ : x ≤ Real.pi
  · exact (by linarith only [hx] : -x/4 ≤ 0).trans (Real.sin_nonneg_of_nonneg_of_le_pi hx hπ)
  · by_cases h4 : x ≤ 4
    · have hπx : Real.pi ≤ x := le_of_not_ge hπ
      have hs := Real.abs_sin_sub_sin_le x Real.pi
      rw [Real.sin_pi, sub_zero, abs_of_nonneg (sub_nonneg.mpr hπx)] at hs
      linarith only [(abs_le.mp hs).1, h4, Real.pi_gt_three]
    · linarith only [Real.neg_one_le_sin x, le_of_not_ge h4]

theorem boundedDurationRatio_lower {N : ℕ} (hN : 0 < N) {u : ℝ} (hu : 0 < u)
    (huπ : u < Real.pi/2) : -(1/4 : ℝ) ≤ boundedDurationRatio N u := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hs : 0 < Real.sin u := Real.sin_pos_of_pos_of_lt_pi hu (by linarith [Real.pi_pos])
  have hc : 0 < Real.cos u := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], huπ⟩
  have ht := Real.le_tan hu.le huπ
  rw [Real.tan_eq_sin_div_cos] at ht
  have huc := (le_div_iff₀ hc).mp ht            -- u * cos u ≤ sin u
  have hsin := sine_lower_quarter (x := (N : ℝ)*u) (by positivity)
  have hmul := mul_le_mul_of_nonneg_left hsin hc.le
  have hscale := mul_le_mul_of_nonneg_left huc (show 0 ≤ (N : ℝ)/4 by positivity)
  unfold boundedDurationRatio
  apply (le_div_iff₀ (mul_pos hNr hs)).mpr
  nlinarith only [hmul, hscale]

theorem uniformHalfCount_cosine_lower_interior {h : ℝ} (hh : 0 < h) {N : ℕ} (hN : 0 < N)
    {u : ℝ} (hu : 0 < u) (huπ : u < Real.pi/2) :
    -(1/4 : ℝ) ≤ cosineSeries (countLawWeight
      (roundedDurationLaw h (uniformDurationLaw ((N : ℝ)*h/2)))) (2*u) := by
  have hc : 0 < Real.cos u := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], huπ⟩
  have hB := boundedDurationRatio_lower hN hu huπ
  rw [uniformHalfCount_cosine_ratio hh hN hu huπ]
  split_ifs
  · linarith only [hB]
  · nlinarith only [hB, hc, Real.cos_le_one u,
      mul_nonneg hc.le (show 0 ≤ boundedDurationRatio N u + 1/4 by linarith only [hB])]

theorem boundedDuration_nonnegative_cosine_and_uniform_comparison {h : ℝ} (hh : 0 < h)
    {N : ℕ} (hN : 0 < N) (θ : ℝ) (hθ : |θ| ≤ Real.pi) :
    let q := cosineSeries (countLawWeight (triangularCountLaw h N)) θ
    let w := cosineSeries
      (countLawWeight (roundedDurationLaw h (uniformDurationLaw ((N : ℝ)*h/2)))) θ
    0 ≤ q ∧ (1/2 : ℝ)*(1-q) ≤ 1-w ∧ -(1/4 : ℝ) ≤ w := by
  let Q := countLawWeight (triangularCountLaw h N)
  let W := countLawWeight (roundedDurationLaw h (uniformDurationLaw ((N : ℝ)*h/2)))
  let : IsProbabilityMeasure (triangularDurationLaw ((N : ℝ)*h)) :=
    triangularDuration_probability (mul_pos (Nat.cast_pos.mpr hN) hh)
  let : IsProbabilityMeasure (uniformDurationLaw ((N : ℝ)*h/2)) :=
    uniformDuration_probability (div_pos (mul_pos (Nat.cast_pos.mpr hN) hh) (by norm_num))
  let : IsProbabilityMeasure (triangularCountLaw h N) := triangularCount_probability hh hN
  change 0 ≤ cosineSeries Q θ ∧ (1/2 : ℝ)*(1 - cosineSeries Q θ) ≤ 1 - cosineSeries W θ ∧
    -(1/4 : ℝ) ≤ cosineSeries W θ
  rw [← cosineSeries_abs_frequency Q θ, ← cosineSeries_abs_frequency W θ]
  by_cases hzero : |θ| = 0
  · have hq : cosineSeries Q 0 = 1 := countLaw_cosine_zero (triangularCountLaw h N)
    have hw : cosineSeries W 0 = 1 :=
      countLaw_cosine_zero (roundedDurationLaw h (uniformDurationLaw ((N : ℝ)*h/2)))
    rw [hzero, hq, hw]
    norm_num
  by_cases hpi : |θ| = Real.pi
  · have hq : cosineSeries Q Real.pi = 0 := roundedDuration_cosine_pi h (triangularDurationLaw ((N : ℝ)*h))
    have hw : cosineSeries W Real.pi = 0 := roundedDuration_cosine_pi h (uniformDurationLaw ((N : ℝ)*h/2))
    rw [hpi, hq, hw]
    norm_num
  let u := |θ|/2
  have hu : 0 < u := div_pos (lt_of_le_of_ne (abs_nonneg θ) (Ne.symm hzero)) (by norm_num)
  have huπ : u < Real.pi/2 := div_lt_div_of_pos_right (lt_of_le_of_ne hθ hpi) (by norm_num)
  have hangle : |θ| = 2*u := by dsimp [u]; ring
  rw [hangle]
  change 0 ≤ cosineSeries (countLawWeight (triangularCountLaw h N)) (2*u) ∧
    (1/2 : ℝ)*(1-cosineSeries (countLawWeight (triangularCountLaw h N)) (2*u)) ≤
      1-cosineSeries (countLawWeight (roundedDurationLaw h (uniformDurationLaw ((N : ℝ)*h/2)))) (2*u) ∧ _
  refine ⟨?_, ?_, uniformHalfCount_cosine_lower_interior hh hN hu huπ⟩
  · rw [triangularCount_cosine_ratio hh hN hu huπ]
    exact sq_nonneg _
  · rw [triangularCount_cosine_ratio hh hN hu huπ, uniformHalfCount_cosine_ratio hh hN hu huπ]
    split_ifs
    · nlinarith only [sq_nonneg (boundedDurationRatio N u - 1)]
    · nlinarith only [sq_nonneg (boundedDurationRatio N u - Real.cos u),
        Real.cos_sq_le_one u]

/-- The triangular row of Lemma 5.4, including the full retained mass. -/
theorem triangular_example_fourier {h : ℝ} (hh : 0 < h) {N : ℕ} (hN : 0 < N) :
    let T := (N : ℝ)*h
    let ρ := triangularDurationLaw T
    let w := roundedDurationLaw h (conditionalDurationLaw ρ T)
    let q := triangularCountLaw h N
    let μJ := roundedDurationLaw h ρ
    ρ (Iic T) = 1 ∧ ∀ θ ∈ Icc (-Real.pi) Real.pi,
      1 * (1 - cosineSeries (countLawWeight q) θ) ≤
        1 - cosineSeries (countLawWeight w) θ ∧
      1 ≤ 1 + cosineSeries (countLawWeight μJ) θ := by
  dsimp only
  let T := (N : ℝ)*h
  let : IsProbabilityMeasure (triangularDurationLaw T) :=
    triangularDuration_probability (mul_pos (Nat.cast_pos.mpr hN) hh)
  have he := conditionalDuration_eq_of_ae_le (triangularDurationLaw T) T
    (triangularDuration_ae.mono fun _ ht => ht.2.le)
  refine ⟨he.1, ?_⟩
  intro θ hθ
  rw [he.2]
  change 1 * (1 - cosineSeries (countLawWeight (triangularCountLaw h N)) θ) ≤
    1 - cosineSeries (countLawWeight (triangularCountLaw h N)) θ ∧
    1 ≤ 1 + cosineSeries (countLawWeight (triangularCountLaw h N)) θ
  exact ⟨by simp, le_add_of_nonneg_right
    (boundedDuration_nonnegative_cosine_and_uniform_comparison hh hN θ (abs_le.mpr hθ)).1⟩

/-- The uniform row of Lemma 5.4, including the full retained mass. -/
theorem uniform_example_fourier {h : ℝ} (hh : 0 < h) {N : ℕ} (hN : 0 < N) :
    let T := (N : ℝ)*h/2
    let ρ := uniformDurationLaw T
    let w := roundedDurationLaw h (conditionalDurationLaw ρ T)
    let q := triangularCountLaw h N
    let μJ := roundedDurationLaw h ρ
    ρ (Iic T) = 1 ∧ ∀ θ ∈ Icc (-Real.pi) Real.pi,
      (1/2 : ℝ) * (1 - cosineSeries (countLawWeight q) θ) ≤
        1 - cosineSeries (countLawWeight w) θ ∧
      (3/4 : ℝ) ≤ 1 + cosineSeries (countLawWeight μJ) θ := by
  dsimp only
  let T := (N : ℝ)*h/2
  let : IsProbabilityMeasure (uniformDurationLaw T) :=
    uniformDuration_probability (div_pos (mul_pos (Nat.cast_pos.mpr hN) hh) (by norm_num))
  have he := conditionalDuration_eq_of_ae_le (uniformDurationLaw T) T
    (uniformDuration_ae.mono fun _ ht => ht.2.le)
  refine ⟨he.1, ?_⟩
  intro θ hθ
  rw [he.2]
  have hb := (boundedDuration_nonnegative_cosine_and_uniform_comparison hh hN θ (abs_le.mpr hθ)).2
  exact ⟨hb.1, by linarith only [hb.2]⟩

end BreakingResonance

#print axioms BreakingResonance.boundedDurationRatio_lower
#print axioms BreakingResonance.uniformHalfCount_cosine_lower_interior
#print axioms BreakingResonance.triangular_example_fourier
#print axioms BreakingResonance.uniform_example_fourier
