import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! Trigonometric inequalities used in the three frequency ranges of Lemma 5.3. -/
namespace BreakingResonance

theorem abs_sin_nat_mul_le (n : ℕ) (x : ℝ) : |Real.sin (n * x)| ≤ n * |Real.sin x| := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ, add_mul, one_mul, Real.sin_add]
    calc
      _ ≤ |Real.sin (↑n * x) * Real.cos x| + |Real.cos (↑n * x) * Real.sin x| :=
        abs_add_le _ _
      _ ≤ |Real.sin (↑n * x)| + |Real.sin x| := by
        rw [abs_mul, abs_mul]
        exact add_le_add
          (mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _))
          (mul_le_of_le_one_left (abs_nonneg _) (Real.abs_cos_le_one _))
      _ ≤ _ := by rw [add_mul, one_mul]; exact add_le_add ih le_rfl

theorem one_sub_cos_nat_mul_le (k : ℕ) (x : ℝ) :
    1 - Real.cos ((k : ℝ)*x) ≤ (k : ℝ)^2 * (1 - Real.cos x) := by
  have h := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (Nat.cast_nonneg k) (abs_nonneg _))).mpr
    (abs_sin_nat_mul_le k (x / 2))
  rw [sq_abs, mul_pow, sq_abs] at h
  have hleft := Real.cos_two_mul_eq_one_sub ((k : ℝ) * (x/2))
  have hright := Real.cos_two_mul_eq_one_sub (x/2)
  rw [show 2 * (↑k * (x/2)) = (k : ℝ)*x by ring] at hleft
  rw [show 2 * (x/2) = x by ring] at hright
  rw [hleft, hright]
  linarith only [h]

theorem one_sub_cos_even_mul_le (k : ℕ) (hk : Even k) (x : ℝ) :
    1 - Real.cos ((k : ℝ)*x) ≤ (k : ℝ)^2 * (1 + Real.cos x) := by
  obtain ⟨n, hn⟩ := hk
  have h := one_sub_cos_nat_mul_le k (x + Real.pi)
  have ht : (k : ℝ) * (x + Real.pi) = k * x + n * (2 * Real.pi) := by
    rw [mul_add]
    congr 1
    rw [hn, Nat.cast_add]
    ring
  rw [ht, Real.cos_add_nat_mul_two_pi, Real.cos_add_pi, sub_neg_eq_add] at h
  exact h

theorem one_sub_cos_le_sq_div_two (x : ℝ) : 1 - Real.cos x ≤ x^2/2 := by
  have h := (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mpr
    (Real.abs_sin_le_abs (x := x/2))
  rw [sq_abs, sq_abs] at h
  conv_lhs => rw [show x = 2 * (x/2) by ring, Real.cos_two_mul_eq_one_sub]
  nlinarith only [h]

theorem sq_div_four_le_one_sub_cos {x : ℝ} (hx : |x| ≤ 1) :
    x^2/4 ≤ 1 - Real.cos x := by
  let y := |x|/2
  have hy : 0 ≤ y := div_nonneg (abs_nonneg x) (by norm_num)
  have hy2 : y ≤ 1/2 := by dsimp [y]; linarith
  have hcube : y^3 ≤ y/4 := by
    have hsq := (sq_le_sq₀ hy (by norm_num : (0 : ℝ) ≤ 1/2)).mpr hy2
    nlinarith only [mul_le_mul_of_nonneg_right hsq hy]
  have hs : (3/4 : ℝ)*y ≤ Real.sin y := by
    linarith only [Real.sin_ge_sub_cube hy, hcube, hy]
  have hsq := (sq_le_sq₀ (by positivity : 0 ≤ (3/4 : ℝ)*y)
    ((by positivity : 0 ≤ (3/4 : ℝ)*y).trans hs)).mpr hs
  rw [← Real.cos_abs, show |x| = 2*y by dsimp [y]; ring, Real.cos_two_mul_eq_one_sub]
  have hyx : x^2 = 4*y^2 := by dsimp [y]; rw [div_pow, sq_abs]; ring
  rw [hyx]
  nlinarith only [hsq, sq_nonneg y]

end BreakingResonance

#print axioms BreakingResonance.one_sub_cos_nat_mul_le
#print axioms BreakingResonance.one_sub_cos_even_mul_le
#print axioms BreakingResonance.one_sub_cos_le_sq_div_two
#print axioms BreakingResonance.sq_div_four_le_one_sub_cos
