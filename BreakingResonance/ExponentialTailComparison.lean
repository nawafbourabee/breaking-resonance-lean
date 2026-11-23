import BreakingResonance.ExponentialDurationCutoff
import BreakingResonance.ExponentialFourierComparison

/-! The effect of the exponential cutoff on the Fourier comparison. -/
noncomputable section
namespace BreakingResonance
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

theorem one_sub_cos_add_le_twice (a b : ℝ) :
    1-Real.cos (a+b) ≤ 2*(1-Real.cos a)+2*(1-Real.cos b) := by
  have hid (t : ℝ) : 1-Real.cos t = 2*Real.sin (t/2)^2 := by
    have h := Real.cos_two_mul_eq_one_sub (t/2)
    rw [show 2*(t/2) = t by ring] at h
    linarith only [h]
  have hb : |Real.sin ((a+b)/2)| ≤ |Real.sin (a/2)|+|Real.sin (b/2)| := by
    rw [show (a+b)/2 = a/2+b/2 by ring, Real.sin_add]
    exact (abs_add_le _ _).trans (by
      rw [abs_mul, abs_mul]
      exact add_le_add
        (mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _))
        (mul_le_of_le_one_left (abs_nonneg _) (Real.abs_cos_le_one _)))
  have hb₂ := (sq_le_sq₀ (abs_nonneg _) (add_nonneg (abs_nonneg _) (abs_nonneg _))).mpr hb
  rw [sq_abs] at hb₂
  have hc := sq_nonneg (|Real.sin (a/2)| - |Real.sin (b/2)|)
  rw [hid, hid, hid]
  nlinarith only [hb₂, hc, sq_abs (Real.sin (a/2)), sq_abs (Real.sin (b/2))]

theorem sinc_sq_gap {x : ℝ} (hx : 0 < x) :
    (2/7 : ℝ)*min (x^2) 1 ≤ 1-(Real.sin x/x)^2 := by
  by_cases hsmall : x ≤ 1
  · have hxπ : x ≤ Real.pi := hsmall.trans (by linarith only [Real.pi_gt_three])
    have hs : 0 ≤ Real.sin x/x :=
      div_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hx.le hxπ) hx.le
    have hsinc : Real.sin x/x ≤ 1 - x^2/6 + x^4/120 := by
      apply (div_le_iff₀ hx).mpr
      nlinarith only [sine_le_degree_five x hx.le]
    have hx2 : x^2 ≤ 1 := by
      simpa only [one_pow] using (sq_le_sq₀ hx.le zero_le_one).mpr hsmall
    have hx4 : x^4 ≤ x^2 := by
      nlinarith only [mul_le_mul_of_nonneg_right hx2 (sq_nonneg x)]
    have hupper : Real.sin x/x ≤ 1-(19/120 : ℝ)*x^2 := by
      linarith only [hsinc,hx4]
    have hsquared := (sq_le_sq₀ hs (hs.trans hupper)).mpr hupper
    rw [min_eq_left hx2]
    nlinarith only [hsquared,hx4,sq_nonneg x]
  · have h1 : 1 ≤ x := le_of_not_ge hsmall
    have hs : |Real.sin x/x| ≤ Real.sin 1 := by
      by_cases hxπ : x ≤ Real.pi
      · rw [abs_of_nonneg (div_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hx.le hxπ) hx.le)]
        have he := sine_div_antitone
          (show (1:ℝ) ∈ Ioc 0 Real.pi from ⟨by norm_num, by linarith only [Real.pi_gt_three]⟩)
          (show x ∈ Ioc 0 Real.pi from ⟨hx,hxπ⟩) h1
        simpa only [div_one] using he
      · rw [abs_div, abs_of_pos hx]
        have hx3 : 3 ≤ x := (le_of_lt Real.pi_gt_three).trans (le_of_not_ge hxπ)
        have hs3 : (1/3 : ℝ) ≤ Real.sin 1 := by
          linarith only [Real.sin_ge_sub_cube (by norm_num : (0:ℝ) ≤ 1)]
        calc
          _ ≤ 1/x := div_le_div_of_nonneg_right (Real.abs_sin_le_one _) hx.le
          _ ≤ 1/3 := div_le_div_of_nonneg_left zero_le_one (by norm_num) hx3
          _ ≤ _ := hs3
    have hsin₀ : 0 ≤ Real.sin 1 := (abs_nonneg _).trans hs
    have hsq := (sq_le_sq₀ (abs_nonneg _) hsin₀).mpr hs
    rw [sq_abs] at hsq
    have hsin : Real.sin 1 ≤ (101/120 : ℝ) := by
      calc
        _ ≤ 1-1^3/6+1^5/120 := sine_le_degree_five 1 zero_le_one
        _ = _ := by norm_num
    have hsin₂ := (sq_le_sq₀ hsin₀ (by norm_num : 0 ≤ (101/120:ℝ))).mpr hsin
    have hx2 : (1:ℝ) ≤ x^2 := by
      simpa only [one_pow] using (sq_le_sq₀ zero_le_one hx.le).mpr h1
    rw [min_eq_right hx2]
    nlinarith only [hsin₂, hsq]

theorem triangularReference_gap_lower {N : ℕ} (hN : 0 < N) {u : ℝ} (hu : 0 < u)
    (huπ : u < Real.pi/2) :
    (2/7 : ℝ)*min (((N : ℝ)*u)^2) 1 ≤ 1-boundedDurationRatio N u^2 := by
  let x := (N : ℝ)*u
  let v := (N : ℝ)*Real.tan u
  have hNr : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hx : 0 < x := mul_pos hNr hu
  have hv : 0 < v := mul_pos hNr (Real.tan_pos_of_pos_of_lt_pi_div_two hu huπ)
  have hvx : x ≤ v := mul_le_mul_of_nonneg_left (Real.le_tan hu.le huπ) hNr.le
  have hb : |boundedDurationRatio N u| ≤ |Real.sin x/x| := by
    rw [boundedDurationRatio_sine_div hu huπ]
    change |Real.sin x/v| ≤ |Real.sin x/x|
    rw [abs_div, abs_div, abs_of_pos hv, abs_of_pos hx]
    exact div_le_div_of_nonneg_left (abs_nonneg _) hx hvx
  have hsq := (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mpr hb
  rw [sq_abs, sq_abs] at hsq
  exact (sinc_sq_gap hx).trans (sub_le_sub_left hsq 1)

theorem exponentialCutoff_shift_comparison {h : ℝ} (hh : 0 < h) {N : ℕ} (hN : 0 < N)
    (θ : ℝ) (hθ : |θ| ≤ Real.pi) :
    1-Real.cos (((2*N : ℕ) : ℝ)*θ) ≤
      28*(1-cosineSeries (countLawWeight (triangularCountLaw h N)) θ) := by
  let Q := countLawWeight (triangularCountLaw h N)
  let : IsProbabilityMeasure (triangularCountLaw h N) := triangularCount_probability hh hN
  have hN₀ : 0 ≤ (((2*N : ℕ) : ℝ)) := Nat.cast_nonneg _
  have hangle : Real.cos (((2*N : ℕ) : ℝ)*|θ|) = Real.cos (((2*N : ℕ) : ℝ)*θ) := by
    rw [← Real.cos_abs (((2*N : ℕ) : ℝ)*θ), abs_mul,
      abs_of_nonneg hN₀]
  change _ ≤ 28*(1-cosineSeries Q θ)
  rw [← hangle, ← cosineSeries_abs_frequency Q θ]
  by_cases hzero : |θ| = 0
  · have hq : cosineSeries Q 0 = 1 := countLaw_cosine_zero (triangularCountLaw h N)
    rw [hzero,hq,mul_zero,Real.cos_zero]
    norm_num
  by_cases hpi : |θ| = Real.pi
  · let : IsProbabilityMeasure (triangularDurationLaw ((N : ℝ)*h)) :=
      triangularDuration_probability (by positivity)
    have hq : cosineSeries Q Real.pi = 0 :=
      roundedDuration_cosine_pi h (triangularDurationLaw ((N : ℝ)*h))
    rw [hpi,hq]
    linarith only [Real.neg_one_le_cos (((2*N : ℕ):ℝ)*Real.pi)]
  let u := |θ|/2
  let x := (N : ℝ)*u
  have hu : 0 < u := div_pos (lt_of_le_of_ne (abs_nonneg θ) (Ne.symm hzero)) (by norm_num)
  have huπ : u < Real.pi/2 := div_lt_div_of_pos_right (lt_of_le_of_ne hθ hpi) (by norm_num)
  have he : |θ| = 2*u := by dsimp [u]; ring
  have hb : (((2*N : ℕ) : ℝ)*(2*u)) = 4*x := by unfold x; push_cast; ring
  rw [he,hb,triangularCount_cosine_ratio hh hN hu huπ]
  have hax : 1-Real.cos (4*x) ≤ 8*min (x^2) 1 := by
    by_cases hs : x^2 ≤ 1
    · rw [min_eq_left hs]
      nlinarith only [one_sub_cos_le_sq_div_two (4*x)]
    · rw [min_eq_right (le_of_not_ge hs)]
      linarith only [Real.neg_one_le_cos (4*x)]
  exact hax.trans (by linarith only [triangularReference_gap_lower hN hu huπ])

theorem exponentialCutoff_numeric : Real.exp (-8) < 1/2980 := by
  have hsum : (2980:ℝ) < ∑ j ∈ Finset.range 31, (8:ℝ)^j/(j.factorial : ℝ) := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have h : (2980:ℝ) < Real.exp 8 := hsum.trans_le
    (Real.sum_le_exp_of_nonneg (by norm_num) 31)
  rw [Real.exp_neg, ← one_div]
  exact one_div_lt_one_div_of_lt (by norm_num) h

end BreakingResonance

#print axioms BreakingResonance.exponentialCutoff_shift_comparison
#print axioms BreakingResonance.exponentialCutoff_numeric
