import Mathlib

/-! The scalar recurrence in the proof of Proposition A and the final
parameter substitution in Theorem 1. The weak Poincare inequality and
its application to the actual Markov operator are separate obligations. -/
namespace BreakingResonance
noncomputable section

theorem variance_recurrence (V D : ℕ → ℝ) (β φ s M : ℝ)
    (hβ : 0 ≤ β) (hφ : 0 < φ)
    (hpoincare : ∀ n, V n ≤ 2 / φ ^ 2 * D n + 2 * s * M ^ 2)
    (hspectral : ∀ n, β * D n ≤ V n - V (n+1)) (n : ℕ) :
    V (n+1) ≤ (1 - β * φ ^ 2 / 2) * V n + β * φ ^ 2 * s * M ^ 2 := by
  have hmul := mul_le_mul_of_nonneg_left (hpoincare n)
    (show 0 ≤ φ ^ 2 / 2 by positivity)
  have hφ2 : φ ^ 2 ≠ 0 := ne_of_gt (by positivity)
  have hclean : φ ^ 2 / 2 * (2 / φ ^ 2 * D n + 2 * s * M ^ 2) =
      D n + φ ^ 2 * s * M ^ 2 := by field_simp
  rw [hclean] at hmul
  have hm := mul_le_mul_of_nonneg_left hmul hβ
  nlinarith [hspectral n]

theorem affine_decay (V : ℕ → ℝ) (q A B : ℝ)
    (hq : 0 ≤ q) (hstart : V 0 ≤ A)
    (hstep : ∀ n, V (n+1) ≤ q * V n + (1-q) * B) :
    ∀ n, V n ≤ q ^ n * A + (1 - q ^ n) * B := by
  intro n
  induction n with
  | zero => simpa using hstart
  | succ n ih =>
    have hm := mul_le_mul_of_nonneg_left ih hq
    rw [pow_succ]
    nlinarith [hstep n]

theorem affine_decay_exp (V : ℕ → ℝ) (rate A B : ℝ)
    (_hrate : 0 ≤ rate) (hrate1 : rate ≤ 1) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hstart : V 0 ≤ A)
    (hstep : ∀ n, V (n+1) ≤ (1-rate) * V n + rate * B) (n : ℕ) :
    V n ≤ Real.exp (-(n : ℝ) * rate) * A + B := by
  have hd := affine_decay V (1-rate) A B (by linarith) hstart (by
    intro j; convert hstep j using 1
    ring) n
  have hq : 0 ≤ (1-rate) ^ n := pow_nonneg (by linarith) n
  have he : 1-rate ≤ Real.exp (-rate) := by linarith [Real.add_one_le_exp (-rate)]
  have hpow := pow_le_pow_left₀ (by linarith : 0 ≤ 1-rate) he n
  have hexp : Real.exp (-rate) ^ n = Real.exp (-(n : ℝ) * rate) := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  rw [hexp] at hpow
  have hm := mul_le_mul_of_nonneg_right hpow hA
  nlinarith [mul_nonneg hq hB]

theorem theoremOne_mass_substitution (M ε : ℝ) (hM : 0 < M) (hε : 0 < ε) :
    2 * (ε ^ 4 / (64 * M ^ 4)) * (4 * M ^ 2 / ε) ^ 2 = ε ^ 2 / 2 := by
  field_simp
  ring

theorem theoremOne_error_bound (M ε β φ n t : ℝ)
    (hM : 0 < M) (hε : 0 < ε) (hβ : 0 < β) (hφ : 0 < φ)
    (hn : 2 / (β * φ ^ 2) * Real.log (8 * M ^ 2 / ε ^ 3) ≤ n)
    (ht : t ≤ ε / 2 + 1 / 2 * Real.sqrt
      (Real.exp (-n * β * φ ^ 2 / 2) * (4 * M ^ 2 / ε) + ε ^ 2 / 2)) :
    t ≤ ε := by
  have hden : 0 < β * φ ^ 2 := by positivity
  have harg : 0 < 8 * M ^ 2 / ε ^ 3 := by positivity
  have hm := mul_le_mul_of_nonneg_right hn (le_of_lt (half_pos hden))
  have heq : (2 / (β * φ ^ 2) * Real.log (8 * M ^ 2 / ε ^ 3)) *
      (β * φ ^ 2 / 2) = Real.log (8 * M ^ 2 / ε ^ 3) := by field_simp
  rw [heq] at hm
  have he : Real.exp (-n * β * φ ^ 2 / 2) ≤ (8 * M ^ 2 / ε ^ 3)⁻¹ := by
    rw [← Real.exp_log harg, ← Real.exp_neg]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hmul := mul_le_mul_of_nonneg_right he (by positivity : 0 ≤ 4 * M ^ 2 / ε)
  have hcancel : (8 * M ^ 2 / ε ^ 3)⁻¹ * (4 * M ^ 2 / ε) = ε ^ 2 / 2 := by
    field_simp
    ring
  rw [hcancel] at hmul
  have hs : Real.sqrt (Real.exp (-n * β * φ ^ 2 / 2) *
      (4 * M ^ 2 / ε) + ε ^ 2 / 2) ≤ ε := by
    apply (Real.sqrt_le_left hε.le).mpr
    linarith
  linarith

end
end BreakingResonance
