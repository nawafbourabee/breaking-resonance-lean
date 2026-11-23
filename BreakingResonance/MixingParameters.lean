import BreakingResonance.DurationNonresonance
import BreakingResonance.ConductanceNumerics
import PersistencePays.GibbsTail

noncomputable section

open MeasureTheory ProbabilityTheory Set PersistencePays
open scoped ENNReal

namespace BreakingResonance

/-- The duration cutoff in the proof of Theorem 1. -/
theorem duration_cutoff_tail (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    {m b δ : ℝ} (hρ : NonresonantDuration ρ m b δ) :
    let τstar := 4*b/(δ*Real.sqrt m)
    0 < τstar ∧ ρ.real (Ioi τstar) ≤ δ/4 := by
  let τstar := 4*b/(δ*Real.sqrt m)
  have hsqrt := Real.sqrt_pos.mpr hρ.m_pos
  have hb := hρ.b_pos
  have hδ := hρ.gap_pos
  have hcut : 0 < τstar := by dsimp [τstar]; positivity
  refine ⟨hcut,?_⟩
  have hi := hρ.integrable_duration.div_const τstar
  have hf (τ : ℝ) (hτ : τ ∈ Ioi τstar) : 1 ≤ τ/τstar :=
    (le_div_iff₀ hcut).mpr (by simpa using hτ.le)
  have hle := hi.measure_le_integral (hρ.positive_ae.mono fun τ hτ =>
    div_nonneg hτ.le hcut.le) hf
  have htarget : (b/Real.sqrt m)/τstar = δ/4 := by
    dsimp [τstar]
    field_simp [hb.ne',hδ.ne',hsqrt.ne']
  have hJ := div_le_div_of_nonneg_right hρ.mean_le hcut.le
  rw [htarget] at hJ
  have hi' : (∫ x, x/τstar ∂ρ) = (∫ x, x ∂ρ)/τstar := integral_div _ _
  have hi₀ : 0 ≤ ∫ x, x/τstar ∂ρ := integral_nonneg_of_ae
    (hρ.positive_ae.mono fun _ hτ => div_nonneg hτ.le hcut.le)
  have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
  change ρ.real (Ioi τstar) ≤ (ENNReal.ofReal (∫ x, x/τstar ∂ρ)).toReal at ht
  rw [ENNReal.toReal_ofReal hi₀,hi'] at ht
  exact ht.trans hJ

theorem retained_duration_lower (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    {δ τstar : ℝ} (h : ρ.real (Ioi τstar) ≤ δ/4) :
    1-δ/4 ≤ ρ.real (Iic τstar) := by
  have he := measureReal_add_measureReal_compl (μ := ρ) (measurableSet_Iic (a := τstar))
  rw [probReal_univ,compl_Iic] at he
  linarith only [he,h]

theorem mixing_cutoff_parameters {M ε η : ℝ} (hM : 1 ≤ M) (hε : 0 < ε)
    (hε₁ : ε ≤ 1) (hη : 0 < η) (hη₁ : η ≤ 1/600) (d : ℕ) :
    let s := ε^4/(64*M^4)
    let D := 1+(d:ℝ)+Real.log (M/ε)
    let R := 3*(d:ℝ)*Real.log 2+2*Real.log (1/(η*s))
    let CR := 2*Real.log (64/η)
    (0 < s ∧ s ≤ 1/64) ∧ 1 ≤ D ∧ 1 ≤ R ∧ R ≤ CR*D ∧ 0 < CR ∧
      (2:ℝ)^(3*(d:ℝ)/2)*Real.exp (-R/2) = η*s := by
  let s := ε^4/(64*M^4)
  let D := 1+(d:ℝ)+Real.log (M/ε)
  let R := 3*(d:ℝ)*Real.log 2+2*Real.log (1/(η*s))
  let CR := 2*Real.log (64/η)
  have hM₀ : 0 < M := by linarith
  have hs : 0 < s := by dsimp [s]; positivity
  have hs₁ : s ≤ 1/64 := by
    have hep : ε^4 ≤ M^4 := pow_le_pow_left₀ hε.le (by linarith only [hM,hε₁]) _
    apply (div_le_iff₀ (by positivity : 0 < 64*M^4)).mpr
    linarith only [hep]
  have hx : 0 ≤ Real.log (M/ε) :=
    Real.log_nonneg ((one_le_div hε).mpr (by linarith only [hM,hε₁]))
  have hCR : 8 ≤ CR := by
    have η₁ : η ≤ 1 := by linarith only [hη₁]
    have hle : Real.log 64 ≤ Real.log (64/η) :=
      Real.log_le_log (by norm_num) ((le_div_iff₀ hη).mpr (by linarith only [η₁]))
    have hl := Real.log_pow (2:ℝ) 6
    norm_num at hl
    dsimp [CR]
    linarith only [hle,hl,log_two_bounds.1]
  have hlog : Real.log (1/(η*s)) = Real.log (64/η)+4*Real.log (M/ε) := by
    have he : 1/(η*s) = (64/η)*(M/ε)^4 := by dsimp [s]; field_simp
    rw [he,Real.log_mul (by positivity : 64/η ≠ 0) (by positivity : (M/ε)^4 ≠ 0),
      Real.log_pow]
    norm_num
  have he : R = 3*(d:ℝ)*Real.log 2+CR+8*Real.log (M/ε) := by
    dsimp [R,CR]
    rw [hlog]
    ring
  have hd : 0 ≤ (d:ℝ) := by positivity
  refine ⟨⟨hs,hs₁⟩,?_,?_,?_,by linarith only [hCR],?_⟩
  · linarith only [hd,hx]
  · change 1 ≤ R
    rw [he]
    nlinarith only [hCR,hx,mul_nonneg hd (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2))]
  · change R ≤ CR*D
    rw [he]
    dsimp [D]
    have hl := log_two_bounds.2
    nlinarith only [mul_le_mul_of_nonneg_right (show 3*Real.log 2 ≤ CR by linarith only [hl,hCR]) hd,
      mul_le_mul_of_nonneg_right hCR hx]
  · rw [Real.rpow_def_of_pos (by norm_num : 0 < (2:ℝ)), ← Real.exp_add]
    have hcancel : Real.log 2*(3*(d:ℝ)/2)+(-R/2) = -(Real.log (1/(η*s))) := by
      dsimp [R]
      ring
    rw [hcancel, one_div,Real.log_inv,neg_neg,Real.exp_log (mul_pos hη hs)]

theorem mixing_iteration_threshold {M ε β φ : ℝ} (hM : 1 ≤ M)
    (hε : 0 < ε) (hβ : 0 < β) (hφ : 0 < φ) {n : ℕ}
    (hn : 6/(β*φ^2)*Real.log (2*M/ε) ≤ (n:ℝ)) :
    2/(β*φ^2)*Real.log (8*M^2/ε^3) ≤ (n:ℝ) := by
  have hM₀ : 0 < M := by linarith
  have harg : 8*M^2/ε^3 ≤ (2*M/ε)^3 := by
    rw [div_pow]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have hm := mul_le_mul_of_nonneg_left hM (sq_nonneg M)
    nlinarith only [hm]
  have hl := Real.log_le_log (show 0 < 8*M^2/ε^3 by positivity) harg
  rw [Real.log_pow] at hl
  have hm := mul_le_mul_of_nonneg_left hl (show 0 ≤ 2/(β*φ^2) by positivity)
  refine hm.trans_eq ?_ |>.trans hn
  push_cast
  ring

end BreakingResonance

#print axioms BreakingResonance.duration_cutoff_tail
#print axioms BreakingResonance.mixing_cutoff_parameters
#print axioms BreakingResonance.mixing_iteration_threshold
