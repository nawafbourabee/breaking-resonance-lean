import BreakingResonance.ExponentialCountLaw
import BreakingResonance.ExponentialTrigBounds

/-! Fourier comparison of the full exponential law with the triangular reference. -/
noncomputable section
namespace BreakingResonance
open MeasureTheory ProbabilityTheory Set

theorem boundedDurationRatio_sine_div {N : ℕ} {u : ℝ} (hu : 0 < u) (huπ : u < Real.pi/2) :
    boundedDurationRatio N u = Real.sin ((N : ℝ)*u)/((N : ℝ)*Real.tan u) := by
  have hc := Real.cos_pos_of_mem_Ioo (show u ∈ Ioo (-(Real.pi/2)) (Real.pi/2) from
    ⟨by linarith [Real.pi_pos], huπ⟩)
  unfold boundedDurationRatio
  rw [Real.tan_eq_sin_div_cos, ← mul_div_assoc, div_div_eq_mul_div, mul_comm (Real.sin _) (Real.cos _)]

theorem exponentialCount_gap_lower {s h : ℝ} (hs : 0 < s) (hh : 0 < h)
    {N : ℕ} (hN : 0 < N) (hsh : s*h = 4/(N : ℝ)) {u : ℝ} (hu : 0 < u)
    (huπ : u < Real.pi/2) :
    let y := ((N : ℝ)*Real.tan u)^2
    y/(4+y) ≤ 1-cosineSeries (countLawWeight (roundedDurationLaw h (expMeasure s))) (2*u) := by
  dsimp only
  let r := Real.exp (-(s*h))
  let v := (N : ℝ)*Real.tan u
  let a := (N : ℝ)*((1-r)/(1+r))
  have hNr : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hc := Real.cos_pos_of_mem_Ioo (show u ∈ Ioo (-(Real.pi/2)) (Real.pi/2) from
    ⟨by linarith [Real.pi_pos], huπ⟩)
  have hr : 0 < r := Real.exp_pos _
  have hr' : r < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr (mul_pos hs hh))
  have ha : 0 < a := mul_pos hNr (div_pos (sub_pos.mpr hr') (by positivity))
  have hv : 0 < v := mul_pos hNr (Real.tan_pos_of_pos_of_lt_pi_div_two hu huπ)
  have ha₂ : a ≤ 2 := by
    have ht : (1-r)/(1+r) ≤ (s*h)/2 := exponential_half_ratio_le (s*h) (by positivity)
    rw [hsh] at ht
    calc
      a ≤ (N : ℝ)*(4/(N : ℝ)/2) := mul_le_mul_of_nonneg_left ht hNr.le
      _ = 2 := by field_simp [hNr.ne']; ring
  have he : cosineSeries (countLawWeight (roundedDurationLaw h (expMeasure s))) (2*u) =
      a^2/(a^2+v^2) := by
    rw [exponentialDuration_cosine_formula hs hh]
    change (1-r)^2*(1+Real.cos (2*u))/(2*(1+r^2-2*r*Real.cos (2*u))) = _
    have h₀ := Real.cos_two_mul u
    have h₁ := Real.sin_sq_add_cos_sq u
    have hD : 1+r^2-2*r*Real.cos (2*u) =
        (1-r)^2*Real.cos u^2+(1+r)^2*Real.sin u^2 := by
      rw [h₀]
      linear_combination -(1+r)^2*h₁
    rw [hD]
    have hcos : 1+Real.cos (2*u) = 2*Real.cos u^2 := by linarith only [h₀]
    rw [hcos]
    unfold a v
    rw [Real.tan_eq_sin_div_cos]
    have hDpos : 0 < (1-r)^2*Real.cos u^2+(1+r)^2*Real.sin u^2 := by
      have hL : 0 < (1-r)^2*Real.cos u^2 :=
        mul_pos (sq_pos_of_pos (sub_pos.mpr hr')) (sq_pos_of_pos hc)
      exact add_pos_of_pos_of_nonneg hL (by positivity)
    field_simp [hDpos.ne', hNr.ne', hc.ne', show 1+r ≠ 0 by positivity]
  change v^2/(4+v^2) ≤ _
  rw [he, show 1-a^2/(a^2+v^2) = v^2/(a^2+v^2) by
    have hn : 0 < a^2+v^2 := by positivity
    field_simp [hn.ne']
    ring]
  apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
  have ha4 := (sq_le_sq₀ ha.le (by norm_num : (0:ℝ) ≤ 2)).mpr ha₂
  linarith only [ha4]

theorem exponentialSinePolynomial_pos {y : ℝ} (hy : 0 ≤ y) (hy' : y ≤ 7) :
    0 < exponentialSinePolynomial y := by
  have hcoef : -1/6+(7+y)/120-(49+7*y+y^2)/5040 ≤ (0 : ℝ) := by
    nlinarith only [hy, hy', sq_nonneg y]
  have hmul := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hy') hcoef
  have hdiff : exponentialSinePolynomial 7 - exponentialSinePolynomial y ≤ 0 := by
    unfold exponentialSinePolynomial
    linear_combination hmul
  exact (by norm_num [exponentialSinePolynomial] : 0 < exponentialSinePolynomial 7).trans_le
    (sub_nonpos.mp hdiff)

theorem exponentialReferencePolynomial_le_ratio_sq {N : ℕ} (hN : 16 ≤ N)
    {u : ℝ} (hu : 0 < u) (huπ : u < Real.pi/2)
    (hy : ((N : ℝ)*Real.tan u)^2 ≤ 7) :
    exponentialReferencePolynomial (((N : ℝ)*Real.tan u)^2) ≤ boundedDurationRatio N u ^ 2 := by
  let v := (N : ℝ)*Real.tan u
  let x := (N : ℝ)*u
  let y := v^2
  have hNr : (16:ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0:ℝ) < N := by linarith only [hNr]
  have ht : 0 < Real.tan u := Real.tan_pos_of_pos_of_lt_pi_div_two hu huπ
  have hv : 0 < v := mul_pos hNp ht
  have hx : 0 < x := mul_pos hNp hu
  have hxy : x ≤ v := mul_le_mul_of_nonneg_left (Real.le_tan hu.le huπ) hNp.le
  have hyt : y ≤ 7 := hy
  have hvπ : v < Real.pi := by
    have hv3 : v < 3 := by
      by_contra! hv3
      have h3 := (sq_le_sq₀ (by norm_num : (0:ℝ) ≤ 3) hv.le).mpr hv3
      change v^2 ≤ 7 at hyt
      linarith only [h3,hyt]
    exact hv3.trans Real.pi_gt_three
  have hsinc : exponentialSinePolynomial y ≤ Real.sin x/x := by
    refine le_trans ?_ (sine_div_antitone ⟨hx,hxy.trans hvπ.le⟩ ⟨hv,hvπ.le⟩ hxy)
    apply (le_div_iff₀ hv).mpr
    unfold exponentialSinePolynomial y
    nlinarith only [sine_ge_degree_seven v hv.le]
  have hsmall : 1-y/768 ≤ x/v := by
    have har := arctan_ge_degree_three (Real.tan u) ht.le
    rw [Real.arctan_tan (by linarith [Real.pi_pos]) huπ] at har
    have hNs : (16:ℝ)^2 ≤ (N : ℝ)^2 :=
      (sq_le_sq₀ (by norm_num) hNp.le).mpr hNr
    have hc : (Real.tan u)^2/3 ≤ y/768 := by
      unfold y v
      rw [mul_pow]
      nlinarith only [mul_le_mul_of_nonneg_right hNs (sq_nonneg (Real.tan u))]
    have hm := mul_le_mul_of_nonneg_right hc ht.le
    have hstep : (1-y/768)*Real.tan u ≤ u := by nlinarith only [hm,har]
    apply (le_div_iff₀ hv).mpr
    unfold x v
    calc
      (1-y/768)*v = (N : ℝ)*((1-y/768)*Real.tan u) := by unfold v; ring
      _ ≤ x := mul_le_mul_of_nonneg_left hstep hNp.le
  have hpos : 0 < exponentialSinePolynomial y :=
    exponentialSinePolynomial_pos (sq_nonneg _) hyt
  have hm : (1-y/768)*exponentialSinePolynomial y ≤ boundedDurationRatio N u := by
    rw [boundedDurationRatio_sine_div hu huπ]
    change _ ≤ Real.sin x/v
    calc
      _ ≤ (x/v)*(Real.sin x/x) :=
        mul_le_mul hsmall hsinc hpos.le (div_nonneg hx.le hv.le)
      _ = Real.sin x/v := by field_simp [hx.ne']
  have hnn : 0 ≤ (1-y/768)*exponentialSinePolynomial y :=
    mul_nonneg (by linarith only [hyt]) hpos.le
  change exponentialReferencePolynomial y ≤ _
  unfold exponentialReferencePolynomial
  rw [← mul_pow]
  exact (sq_le_sq₀ hnn (hnn.trans hm)).mpr hm

theorem exponentialCount_full_comparison {s h : ℝ} (hs : 0 < s) (hh : 0 < h)
    {N : ℕ} (hN : 16 ≤ N) (hsh : s*h = 4/(N : ℝ)) (θ : ℝ) (hθ : |θ| ≤ Real.pi) :
    (5/8 : ℝ)*(1-cosineSeries (countLawWeight (triangularCountLaw h N)) θ) ≤
      1-cosineSeries (countLawWeight (roundedDurationLaw h (expMeasure s))) θ := by
  have hNp : 0 < N := by omega
  let : IsProbabilityMeasure (triangularCountLaw h N) := triangularCount_probability hh hNp
  let : IsProbabilityMeasure (expMeasure s) := isProbabilityMeasure_expMeasure hs
  let Q := countLawWeight (triangularCountLaw h N)
  let W := countLawWeight (roundedDurationLaw h (expMeasure s))
  change (5/8 : ℝ)*(1-cosineSeries Q θ) ≤ 1-cosineSeries W θ
  rw [← cosineSeries_abs_frequency Q θ, ← cosineSeries_abs_frequency W θ]
  by_cases hzero : |θ| = 0
  · rw [hzero, countLaw_cosine_zero (triangularCountLaw h N),
      countLaw_cosine_zero (roundedDurationLaw h (expMeasure s))]
    norm_num
  by_cases hpi : |θ| = Real.pi
  · have hq : cosineSeries Q Real.pi = 0 := by
      let : IsProbabilityMeasure (triangularDurationLaw ((N : ℝ)*h)) :=
        triangularDuration_probability (by positivity)
      exact roundedDuration_cosine_pi h (triangularDurationLaw ((N : ℝ)*h))
    have hw : cosineSeries W Real.pi = 0 := roundedDuration_cosine_pi h (expMeasure s)
    rw [hpi,hq,hw]
    norm_num
  let u := |θ|/2
  have hu : 0 < u := div_pos (lt_of_le_of_ne (abs_nonneg θ) (Ne.symm hzero)) (by norm_num)
  have huπ : u < Real.pi/2 := div_lt_div_of_pos_right (lt_of_le_of_ne hθ hpi) (by norm_num)
  have he : |θ| = 2*u := by dsimp [u]; ring
  rw [he, triangularCount_cosine_ratio hh hNp hu huπ]
  let y := ((N : ℝ)*Real.tan u)^2
  have hy : 0 ≤ y := sq_nonneg _
  refine le_trans ?_ (exponentialCount_gap_lower hs hh hNp hsh hu huπ)
  by_cases hy' : y ≤ 7
  · have hpoly := exponentialReferencePolynomial_comparison hy hy'
    have hQ := exponentialReferencePolynomial_le_ratio_sq hN hu huπ hy'
    apply (le_div_iff₀ (by linarith only [hy] : 0 < 4+y)).mpr
    have hd := mul_le_mul_of_nonneg_left (sub_le_sub_left hQ 1)
      (by linarith only [hy] : 0 ≤ (5/8 : ℝ)*(4+y))
    nlinarith only [hd,hpoly]
  · have hlow : (5/8:ℝ) ≤ y/(4+y) := by
      apply (le_div_iff₀ (by linarith only [hy] : 0 < 4+y)).mpr
      linarith only [le_of_not_ge hy']
    exact (by nlinarith only [sq_nonneg (boundedDurationRatio N u)] :
      (5/8:ℝ)*(1-boundedDurationRatio N u^2) ≤ 5/8).trans hlow

end BreakingResonance

#print axioms BreakingResonance.exponentialCount_full_comparison
