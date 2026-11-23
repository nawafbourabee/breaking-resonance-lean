import BreakingResonance.LowerMatrixProduct

noncomputable section

open Matrix
open scoped Matrix Matrix.Norms.Operator

namespace BreakingResonance

private theorem scalar_matrix_norm_le {M : Matrix (Fin 2) (Fin 2) ℝ} {t c d : ℝ}
    (ht : |t| ≤ c) (hM : ‖M‖ ≤ d) (hc : 0 ≤ c) :
    ‖t • M‖ ≤ c*d := by
  rw [norm_smul,Real.norm_eq_abs]
  exact mul_le_mul ht hM (norm_nonneg M) hc

/-- First-order error of the full return, using the angle bounds on the C
matrices. The unusual product bound is on C(b) C(a) itself. -/
theorem orbit_return_remainder_of_bounds
    (Ca Cb Cα Cβ : Matrix (Fin 2) (Fin 2) ℝ) {p δ : ℝ}
    (hp : 7 ≤ p) (hδ : 0 < δ) (hδp : δ ≤ 1/(80*p^2))
    (ha : ‖Ca‖ ≤ 2*p/3) (hb : ‖Cb‖ ≤ 4*p/3)
    (hea : ‖Cα-Ca‖ ≤ p*δ/2) (heb : ‖Cb-Cβ‖ ≤ 5*p*δ/9)
    (hab : ‖Cb*Ca‖ ≤ 4) :
    let Ma := -Real.cos δ • (1 : Matrix (Fin 2) (Fin 2) ℝ)-Real.sin δ • Ca
    let Mb := -Real.cos (δ/2) • (1 : Matrix (Fin 2) (Fin 2) ℝ)+Real.sin (δ/2) • Cb
    ‖Mb*Ma-1-δ • (Cα-(1/2:ℝ) • Cβ)‖ ≤ 3/2*p*δ^2 := by
  let I : Matrix (Fin 2) (Fin 2) ℝ := 1
  let u := 1-Real.cos δ
  let v := 1-Real.cos (δ/2)
  let a := Real.sin δ
  let b := Real.sin (δ/2)
  let Da := u • I-a • Ca
  let Db := v • I+b • Cb
  have hp₀ : 0 ≤ p := by linarith
  have hpδ : p*δ ≤ 1/80 := by
    have hp0 : 0 < p := by linarith
    have h := (le_div_iff₀ (show 0 < 80*p^2 by positivity)).mp hδp
    have h' := (mul_le_mul_of_nonneg_right (show 1 ≤ p by linarith)
      (show 0 ≤ p*δ by positivity))
    nlinarith only [h,h']
  have hδsm : δ ≤ 1/80 := by
    have h := mul_le_mul_of_nonneg_right (show 1 ≤ p by linarith) hδ.le
    nlinarith only [hpδ,h]
  have hu : |u| ≤ δ^2/2 := by
    rw [abs_of_nonneg (sub_nonneg.mpr (Real.cos_le_one _))]
    exact one_sub_cos_le_half_square hδ.le
  have hv : |v| ≤ δ^2/8 := by
    rw [abs_of_nonneg (sub_nonneg.mpr (Real.cos_le_one _))]
    have h := one_sub_cos_le_half_square (t := δ/2) (by positivity)
    linarith only [h]
  have has : |a| ≤ δ := (Real.abs_sin_le_abs (x := δ)).trans_eq (abs_of_nonneg hδ.le)
  have hbs : |b| ≤ δ/2 := (Real.abs_sin_le_abs (x := δ/2)).trans_eq (abs_of_nonneg (by positivity))
  have had : |δ-a| ≤ δ^3/6 := (Real.abs_sub_sin_le δ).trans_eq (by rw [abs_of_nonneg hδ.le])
  have hbd : |b-δ/2| ≤ δ^3/48 := by
    rw [abs_sub_comm]
    have h := Real.abs_sub_sin_le (δ/2)
    rw [abs_of_nonneg (by positivity : 0 ≤ δ/2)] at h
    linarith only [h]
  have hI : ‖I‖ ≤ 1 := by simp [I]
  have hDa : ‖Da+δ • Cα‖ ≤ (2/3)*p*δ^2 := by
    have he : Da+δ • Cα = u • I+(δ-a) • Ca+δ • (Cα-Ca) := by
      dsimp [Da]
      module
    rw [he]
    have h₁ := scalar_matrix_norm_le hu hI (by positivity)
    have h₂ := scalar_matrix_norm_le had ha (by positivity)
    have h₃ := scalar_matrix_norm_le (show |δ| ≤ δ by rw [abs_of_nonneg hδ.le]) hea hδ.le
    have hm := (norm_add_le (u • I+(δ-a) • Ca) (δ • (Cα-Ca))).trans
      (add_le_add ((norm_add_le _ _).trans (add_le_add h₁ h₂)) h₃)
    have hsq := mul_le_mul_of_nonneg_right hp (sq_nonneg δ)
    have hcube := mul_le_mul_of_nonneg_right hδsm (show 0 ≤ p*δ^2 by positivity)
    nlinarith only [hm,hsq,hcube]
  have hDb : ‖Db-(δ/2) • Cβ‖ ≤ (1/3)*p*δ^2 := by
    have he : Db-(δ/2) • Cβ = v • I+(b-δ/2) • Cb+(δ/2) • (Cb-Cβ) := by
      dsimp [Db]
      module
    rw [he]
    have h₁ := scalar_matrix_norm_le hv hI (by positivity)
    have h₂ := scalar_matrix_norm_le hbd hb (by positivity)
    have h₃ := scalar_matrix_norm_le
      (show |δ/2| ≤ δ/2 by rw [abs_of_nonneg (by positivity)]) heb (by positivity)
    have hm := (norm_add_le (v • I+(b-δ/2) • Cb) ((δ/2) • (Cb-Cβ))).trans
      (add_le_add ((norm_add_le _ _).trans (add_le_add h₁ h₂)) h₃)
    have hsq := mul_le_mul_of_nonneg_right hp (sq_nonneg δ)
    have hcube := mul_le_mul_of_nonneg_right hδsm (show 0 ≤ p*δ^2 by positivity)
    nlinarith only [hm,hsq,hcube]
  have hprod : ‖Db*Da‖ ≤ 3*δ^2 := by
    have he : Db*Da = (v*u) • I-(v*a) • Ca+(b*u) • Cb-(b*a) • (Cb*Ca) := by
      dsimp [Da,Db,I]
      simp only [add_mul,mul_sub,smul_mul_assoc,mul_smul_comm,one_mul,mul_one]
      module
    rw [he]
    have h₁ := scalar_matrix_norm_le (show |v*u| ≤ _ by
      rw [abs_mul]; exact mul_le_mul hv hu (abs_nonneg u) (by positivity)) hI
      (show 0 ≤ (δ^2/8)*(δ^2/2) by positivity)
    have h₂ := scalar_matrix_norm_le (show |v*a| ≤ _ by
      rw [abs_mul]; exact mul_le_mul hv has (abs_nonneg a) (by positivity)) ha
      (show 0 ≤ (δ^2/8)*δ by positivity)
    have h₃ := scalar_matrix_norm_le (show |b*u| ≤ _ by
      rw [abs_mul]; exact mul_le_mul hbs hu (abs_nonneg u) (by positivity)) hb
      (show 0 ≤ (δ/2)*(δ^2/2) by positivity)
    have h₄ := scalar_matrix_norm_le (show |b*a| ≤ _ by
      rw [abs_mul]; exact mul_le_mul hbs has (abs_nonneg a) (by positivity)) hab
      (show 0 ≤ (δ/2)*δ by positivity)
    have hm := (norm_sub_le _ ((b*a) • (Cb*Ca))).trans
      (add_le_add ((norm_add_le _ ((b*u) • Cb)).trans
        (add_le_add ((norm_sub_le ((v*u) • I) ((v*a) • Ca)).trans
          (add_le_add h₁ h₂)) h₃)) h₄)
    have hδ₂ : δ^2 ≤ 1 := by
      simpa using (sq_le_sq₀ hδ.le zero_le_one).mpr (by linarith only [hδsm])
    have hquart := mul_le_mul_of_nonneg_right hδ₂ (sq_nonneg δ)
    have hcu := mul_le_mul_of_nonneg_right hpδ (sq_nonneg δ)
    nlinarith only [hm,hquart,hcu]
  have he :
      (-Real.cos (δ/2) • I+Real.sin (δ/2) • Cb) *
        (-Real.cos δ • I-Real.sin δ • Ca)-I-δ • (Cα-(1/2:ℝ) • Cβ) =
        -(Da+δ • Cα)-(Db-(δ/2) • Cβ)+Db*Da := by
    have hA : -Real.cos δ • I-Real.sin δ • Ca = -I+Da := by dsimp [Da,u,a]; module
    have hB : -Real.cos (δ/2) • I+Real.sin (δ/2) • Cb = -I+Db := by dsimp [Db,v,b]; module
    rw [hA,hB]
    dsimp [I]
    simp only [add_mul,mul_add,neg_mul,mul_neg,one_mul,mul_one,smul_sub,smul_smul]
    module
  change ‖(-Real.cos (δ/2) • I+Real.sin (δ/2) • Cb) *
        (-Real.cos δ • I-Real.sin δ • Ca)-I-δ • (Cα-(1/2:ℝ) • Cβ)‖ ≤ _
  rw [he]
  have hsum := (norm_add_le (-(Da+δ • Cα)-(Db-(δ/2) • Cβ)) (Db*Da)).trans
    (add_le_add (norm_sub_le _ _) hprod)
  rw [norm_neg] at hsum
  have hhalf := mul_le_mul_of_nonneg_right hp (sq_nonneg δ)
  nlinarith only [hsum,hDa,hDb,hhalf]

end BreakingResonance

#print axioms BreakingResonance.orbit_return_remainder_of_bounds
