import BreakingResonance.ExponentialTailComparison

/-! The exponential row of Lemma 5.4, with the cutoff and constants in the manuscript. -/
noncomputable section
namespace BreakingResonance
open MeasureTheory ProbabilityTheory Set

/-- Multiplication by the Fourier factor for a count shift moves that shift
inside the expectation. -/
theorem countLaw_shifted_characteristic_re (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (M : ℕ) (θ : ℝ) :
    ((∫ j : ℕ, Complex.exp ((((j : ℝ)*θ : ℝ) : ℂ)*Complex.I) ∂μ) *
      Complex.exp ((((M : ℝ)*θ : ℝ) : ℂ)*Complex.I)).re =
      ∫ j : ℕ, Real.cos ((j : ℝ)*θ + (M : ℝ)*θ) ∂μ := by
  let f (j : ℕ) := Complex.exp ((((j : ℝ)*θ : ℝ) : ℂ)*Complex.I)
  let z := Complex.exp ((((M : ℝ)*θ : ℝ) : ℂ)*Complex.I)
  have hi : Integrable f μ := Integrable.of_bound
    ((measurable_of_countable f).aestronglyMeasurable) 1
    (Filter.Eventually.of_forall fun _ => (Complex.norm_exp_ofReal_mul_I _).le)
  change Complex.re ((∫ j, f j ∂μ)*z) = _
  rw [← integral_mul_const]
  change RCLike.re (∫ j, f j*z ∂μ) = _
  rw [← integral_re (hi.mul_const z)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun j => by
    change (f j*z).re = _
    unfold f z
    rw [← Complex.exp_add, ← add_mul, ← Complex.ofReal_add, Complex.exp_ofReal_mul_I_re]

theorem countLaw_shifted_cosine_gap (μ : Measure ℕ) [IsProbabilityMeasure μ] (M : ℕ)
    (θ : ℝ) :
    1-(∫ j : ℕ, Real.cos ((j : ℝ)*θ + (M : ℝ)*θ) ∂μ) ≤
      2*(1-cosineSeries (countLawWeight μ) θ) + 2*(1-Real.cos ((M : ℝ)*θ)) := by
  let f (j : ℕ) := Real.cos ((j : ℝ)*θ)
  let g (j : ℕ) := Real.cos ((j : ℝ)*θ + (M : ℝ)*θ)
  let c := Real.cos ((M : ℝ)*θ)
  have hf : Integrable f μ := Integrable.of_bound (measurable_of_countable f).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun _ => Real.abs_cos_le_one _)
  have hg : Integrable g μ := Integrable.of_bound (measurable_of_countable g).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun _ => Real.abs_cos_le_one _)
  have hi : Integrable (fun j => 1-g j) μ := (integrable_const _).sub hg
  have hF : Integrable (fun j => 2*(1-f j)) μ :=
    ((integrable_const (1:ℝ)).sub hf).const_mul 2
  have hI : Integrable (fun j => 2*(1-f j) + 2*(1-c)) μ := hF.add (integrable_const _)
  have hm := integral_mono hi hI (fun j => one_sub_cos_add_le_twice ((j : ℝ)*θ) ((M : ℝ)*θ))
  rw [integral_sub (integrable_const _) hg,
    integral_add hF (integrable_const _),
    integral_const_mul, integral_sub (integrable_const _) hf] at hm
  simp only [integral_const, probReal_univ, one_smul] at hm
  rw [countLaw_cosineSeries_eq_integral_cos]
  exact hm

theorem exponentialDuration_conditional_gap {s h : ℝ} (hs : 0 < s) (hh : 0 < h)
    {M : ℕ} (hM : 0 < M) (θ : ℝ) :
    let t := (Real.exp (-(s*h)))^M
    let A := 1-cosineSeries (countLawWeight (roundedDurationLaw h (expMeasure s))) θ
    let B := 1-Real.cos ((M : ℝ)*θ)
    ((1-2*t)*A-2*t*B)/(1-t) ≤
      1-cosineSeries (countLawWeight
        (roundedDurationLaw h (conditionalDurationLaw (expMeasure s) ((M : ℝ)*h)))) θ := by
  dsimp only
  let r := Real.exp (-(s*h))
  let t := r^M
  let z := Complex.exp ((θ : ℂ)*Complex.I)
  let μ := roundedDurationLaw h (expMeasure s)
  let ν := roundedDurationLaw h (conditionalDurationLaw (expMeasure s) ((M : ℝ)*h))
  let : IsProbabilityMeasure (expMeasure s) := isProbabilityMeasure_expMeasure hs
  let : IsProbabilityMeasure (conditionalDurationLaw (expMeasure s) ((M : ℝ)*h)) :=
    exponentialDuration_conditional_probability hs hh hM
  let : IsProbabilityMeasure μ := roundedDurationLaw_probability _ _
  let : IsProbabilityMeasure ν := roundedDurationLaw_probability _ _
  let F := ∫ j : ℕ, Complex.exp ((((j : ℝ)*θ : ℝ) : ℂ)*Complex.I) ∂μ
  let G := ∫ j : ℕ, Complex.exp ((((j : ℝ)*θ : ℝ) : ℂ)*Complex.I) ∂ν
  have hr : 0 < r := Real.exp_pos _
  have hr₁ : r < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr (mul_pos hs hh))
  have ht : 0 ≤ t := pow_nonneg hr.le _
  have ht₁ : t < 1 := pow_lt_one₀ hr.le hr₁ hM.ne'
  have hden : 0 < 1-t := sub_pos.mpr ht₁
  have hcast : (r : ℂ)^M = (t : ℂ) := Complex.ofReal_pow _ _ |>.symm
  have hG : G.re = (F.re-t*(F*z^M).re)/(1-t) := by
    have he := exponentialDuration_conditional_characteristic hs hh hM θ
    change G = F*((1-((r : ℂ)*z)^M)/(1-(r : ℂ)^M)) at he
    rw [he,mul_pow,hcast]
    have hrewrite : F*((1-(t : ℂ)*z^M)/(1-(t : ℂ))) =
        (F-(t : ℂ)*(F*z^M))/((1-t : ℝ):ℂ) := by
      rw [Complex.ofReal_sub, Complex.ofReal_one, ← mul_div_assoc]
      congr 1
      ring
    rw [hrewrite, Complex.div_ofReal_re, Complex.sub_re, Complex.re_ofReal_mul]
  have hz : z^M = Complex.exp ((((M : ℝ)*θ : ℝ) : ℂ)*Complex.I) := by
    unfold z
    rw [← Complex.exp_nat_mul]
    push_cast
    ring_nf
  have hF : cosineSeries (countLawWeight μ) θ = F.re :=
    countLaw_cosineSeries_eq_re_characteristic μ θ
  have hν : cosineSeries (countLawWeight ν) θ = G.re :=
    countLaw_cosineSeries_eq_re_characteristic ν θ
  have hshift := countLaw_shifted_cosine_gap μ M θ
  rw [← countLaw_shifted_characteristic_re μ M θ, ← hz, hF] at hshift
  change ((1-2*t)*(1-cosineSeries (countLawWeight μ) θ)-
    2*t*(1-Real.cos ((M:ℝ)*θ)))/(1-t) ≤ 1-cosineSeries (countLawWeight ν) θ
  rw [hF,hν,hG]
  apply (div_le_iff₀ hden).mpr
  rw [sub_mul 1 ((F.re-t*(F*z^M).re)/(1-t)),one_mul,div_mul_cancel₀ _ hden.ne']
  nlinarith only [mul_le_mul_of_nonneg_left hshift ht]

/-- The exponential example with cutoff 8/√m, retained mass 1-exp(-8),
comparison constant 3/5, and lower spectral constant 1. -/
theorem exponential_example_fourier {m h : ℝ} (hm : 0 < m) (hh : 0 < h)
    {N : ℕ} (hN : 16 ≤ N) (hStep : h = 4/((N : ℝ)*Real.sqrt m)) :
    let τstar := 8/Real.sqrt m
    let ρ := expMeasure (Real.sqrt m)
    let w := roundedDurationLaw h (conditionalDurationLaw ρ τstar)
    let q := triangularCountLaw h N
    let μ := roundedDurationLaw h ρ
    ρ.real (Iic τstar) = 1-Real.exp (-8) ∧
    (ρ (Ioi τstar)).toReal ≤ (3/4 : ℝ)/4 ∧
      ∀ θ ∈ Icc (-Real.pi) Real.pi,
        (3/5 : ℝ)*(1-cosineSeries (countLawWeight q) θ) ≤
          1-cosineSeries (countLawWeight w) θ ∧
        (1:ℝ) ≤ 1+cosineSeries (countLawWeight μ) θ := by
  dsimp only
  let s := Real.sqrt m
  have hs : 0 < s := Real.sqrt_pos.mpr hm
  have hNp : 0 < N := by omega
  have hNr : (0:ℝ) < N := Nat.cast_pos.mpr hNp
  let ρ := expMeasure s
  let : IsProbabilityMeasure ρ := isProbabilityMeasure_expMeasure hs
  let t := Real.exp (-8)
  let q := triangularCountLaw h N
  let : IsProbabilityMeasure q := triangularCount_probability hh hNp
  have ht : 0 < t := Real.exp_pos _
  have ht₁ : t < 1/2980 := exponentialCutoff_numeric
  have hsh : s*h = 4/(N : ℝ) := by
    rw [hStep]
    change s*(4/((N:ℝ)*s)) = _
    field_simp [hs.ne', hNr.ne']
  have hM : 0 < 2*N := Nat.mul_pos (by decide) hNp
  have hτ : (((2*N : ℕ) : ℝ)*h) = 8/s := by
    rw [hStep]
    change (((2*N : ℕ) : ℝ)*(4/((N:ℝ)*s))) = _
    push_cast
    field_simp [hs.ne', hNr.ne']
    ring
  have he : (Real.exp (-(s*h)))^(2*N) = t := by
    rw [← Real.exp_nat_mul, hsh]
    unfold t
    congr 1
    push_cast
    field_simp [hNr.ne']
    ring
  have hret : ρ.real (Iic (8/s)) = 1-t := by
    rw [← hτ, show ρ = expMeasure s from rfl, exponentialDuration_cutoff_mass hs hh, he]
  refine ⟨hret, ?_, ?_⟩
  · change ρ.real (Ioi (8/s)) ≤ _
    have ht' : ρ.real (Ioi (8/s)) = t := by
      rw [← compl_Iic, measureReal_compl measurableSet_Iic, probReal_univ, hret]
      ring
    rw [ht']
    linarith only [ht₁]
  intro θ hθ
  have hθ' : |θ| ≤ Real.pi := abs_le.mpr hθ
  have hpos := exponentialDuration_cosine_nonneg hs hh θ
  refine ⟨?_, by linarith only [hpos]⟩
  let C := 1-cosineSeries (countLawWeight q) θ
  let A := 1-cosineSeries (countLawWeight (roundedDurationLaw h ρ)) θ
  let B := 1-Real.cos (((2*N : ℕ):ℝ)*θ)
  have hC : 0 ≤ C := by
    unfold C
    rw [countLaw_cosineSeries_eq_integral_cos]
    have hi : Integrable (fun j : ℕ => Real.cos ((j:ℝ)*θ)) q :=
      Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable 1
        (Filter.Eventually.of_forall fun _ => Real.abs_cos_le_one _)
    have he := integral_mono hi (integrable_const (1 : ℝ)) (fun j => Real.cos_le_one ((j : ℝ)*θ))
    simpa only [integral_const, probReal_univ, one_smul, sub_nonneg] using he
  have hA : (5/8 : ℝ)*C ≤ A := exponentialCount_full_comparison hs hh hN hsh θ hθ'
  have hB : B ≤ 28*C := exponentialCutoff_shift_comparison hh hNp θ hθ'
  have hrest := exponentialDuration_conditional_gap hs hh hM θ
  dsimp only at hrest
  rw [he,hτ] at hrest
  change (3/5 : ℝ)*C ≤ _
  refine le_trans ?_ hrest
  have hd : 0 < 1-t := by linarith only [ht₁]
  apply (le_div_iff₀ hd).mpr
  have hco : 0 ≤ 1-2*t := by linarith only [ht₁]
  have hcoef : (3/5 : ℝ)*(1-t) ≤ (1-2*t)*(5/8)-56*t := by linarith only [ht₁]
  calc
    _ = ((3/5 : ℝ)*(1-t))*C := by ring
    _ ≤ ((1-2*t)*(5/8)-56*t)*C := mul_le_mul_of_nonneg_right hcoef hC
    _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_left hA hco,
      mul_le_mul_of_nonneg_left hB (show 0 ≤ 2*t by positivity)]

end BreakingResonance

#print axioms BreakingResonance.exponential_example_fourier
