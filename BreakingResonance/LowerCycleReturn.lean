import BreakingResonance.LowerReturnRemainder

noncomputable section

open Matrix
open scoped Matrix Matrix.Norms.Operator

namespace BreakingResonance

def cycleReturnMatrix (p : ℕ) (δ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  harmonicMatrix (fastAngleNeg p δ)^(2*p) * harmonicMatrix (fastAnglePos p δ)^p

def cycleExpansionCoefficient (p : ℕ) : ℝ :=
  let β := Real.pi/(2*(p:ℝ))
  Real.tan (β/2)/(2*Real.cos β)

theorem cycleReturnMatrix_det (p : ℕ) (δ : ℝ) :
    (cycleReturnMatrix p δ).det = 1 := by
  simp [cycleReturnMatrix,Matrix.det_mul,Matrix.det_pow,harmonicMatrix_det]

set_option maxHeartbeats 450000 in
/-- The full return is its first-order expansion at the unperturbed angles,
up to the remainder in the proof of Lemma 7.1. -/
theorem cycleReturn_remainder {p : ℕ} (hp : 7 ≤ p) {δ : ℝ}
    (hδ : 0 < δ) (hδp : δ ≤ 1/(80*(p:ℝ)^2)) :
    let α := Real.pi/(p:ℝ)
    let β := Real.pi/(2*(p:ℝ))
    ‖cycleReturnMatrix p δ-1-δ • (orbitC α-(1/2:ℝ) • orbitC β)‖ ≤
      3/2*(p:ℝ)*δ^2 := by
  let α := Real.pi/(p:ℝ)
  let β := Real.pi/(2*(p:ℝ))
  let a := fastAnglePos p δ
  let b := fastAngleNeg p δ
  have hp₇ : 7 ≤ (p:ℝ) := by exact_mod_cast hp
  have hp₀ : 0 < (p:ℝ) := by linarith
  have hπ := Real.pi_pos
  obtain ⟨hb,hb₃,hba,haπ,hab,hpa,hpb⟩ := fastAngle_bounds hp hδ hδp
  have hα : 0 < α := by positivity
  have hβ : 0 < β := by positivity
  have ha : 0 < a := hb.trans hba
  have hαa : α ≤ a := div_le_div_of_nonneg_right (by linarith only [hδ]) hp₀.le
  have hbβ : b ≤ β := div_le_div_of_nonneg_right (by linarith only [hδ]) (by positivity)
  have hαa' : a-α = δ/(p:ℝ) := by
    simp only [a,fastAnglePos,α,add_div,add_sub_cancel_left]
  have hbβ' : β-b = δ/(4*(p:ℝ)) := by
    dsimp [β,b,fastAngleNeg]
    field_simp
    ring
  have ha' : a < Real.pi/2 := by linarith only [haπ,hπ]
  have hβ' : β < Real.pi/2 := (div_lt_iff₀ (by positivity)).mpr (by
    have hm := mul_le_mul_of_nonneg_right hp₇ hπ.le
    nlinarith only [hm,hπ])
  have hα₃ : 3/(p:ℝ) ≤ α :=
    div_le_div_of_nonneg_right Real.pi_gt_three.le hp₀.le
  have hCa : ‖orbitC a‖ ≤ 2*(p:ℝ)/3 := (orbitC_norm_le (hα.trans_le hαa) ha').trans (by
    apply (div_le_iff₀ (hα.trans_le hαa)).mpr
    have h := (div_le_iff₀ hp₀).mp (hα₃.trans hαa)
    nlinarith only [h])
  have hCb : ‖orbitC b‖ ≤ 4*(p:ℝ)/3 := (orbitC_norm_le hb (hbβ.trans_lt hβ')).trans (by
    apply (div_le_iff₀ hb).mpr
    have h := (div_le_iff₀ (by positivity : 0 < 2*(p:ℝ))).mp hb₃
    nlinarith only [h])
  have hda : ‖orbitC α-orbitC a‖ ≤ (p:ℝ)*δ/2 := by
    rw [norm_sub_rev]
    apply (orbitC_difference hα hαa ha').trans
    rw [hαa']
    apply (div_le_iff₀ (by positivity : 0 < 2*α*a)).mpr
    have h := mul_le_mul_of_nonneg_left hαa
      (show 0 ≤ (p:ℝ)*δ*α by positivity)
    have he : Real.pi^2*(δ/(p:ℝ)) = (p:ℝ)*δ*α*α := by
      dsimp [α]
      field_simp
    rw [he]
    nlinarith only [h]
  have hdb : ‖orbitC b-orbitC β‖ ≤ 5*(p:ℝ)*δ/9 := by
    rw [norm_sub_rev]
    apply (orbitC_difference hb hbβ hβ').trans
    rw [hbβ']
    apply (div_le_iff₀ (by positivity : 0 < 2*b*β)).mpr
    have hb₀ := (div_le_iff₀ (by positivity : 0 < 2*(p:ℝ))).mp hb₃
    have hβ₀ : 3 ≤ β*(2*(p:ℝ)) := hb₀.trans
      (mul_le_mul_of_nonneg_right hbβ (by positivity))
    have hprod := mul_le_mul hb₀ hβ₀ (by norm_num : (0:ℝ) ≤ 3) (by positivity)
    have hπ₂ : Real.pi^2 ≤ 10 := by
      nlinarith only [(sq_le_sq₀ hπ.le (by norm_num : (0:ℝ) ≤ 3.15)).mpr Real.pi_lt_d2.le]
    have hleft := mul_le_mul_of_nonneg_right hπ₂ (show 0 ≤ δ/(4*(p:ℝ)) by positivity)
    have hright := mul_le_mul_of_nonneg_right hprod (show 0 ≤ 5*δ/(18*(p:ℝ)) by positivity)
    have hkey : 10*(δ/(4*(p:ℝ))) = 3*3*(5*δ/(18*(p:ℝ))) := by ring
    have heq : b*(2*(p:ℝ))*(β*(2*(p:ℝ)))*(5*δ/(18*(p:ℝ))) =
        5*(p:ℝ)*δ/9*(2*b*β) := by field_simp; ring
    rw [hkey] at hleft
    rw [heq] at hright
    exact hleft.trans hright
  have hac := orbitC_product_norm_le_four hb hba.le haπ hab
  have hsA : Real.sin a ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi (hα.trans_le hαa) (by linarith only [haπ,hπ])).ne'
  have hsB : Real.sin b ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi hb (by linarith only [hbβ,hβ',hπ])).ne'
  have hp₂ : ((2*p:ℕ):ℝ)*b = Real.pi-δ/2 := by push_cast; exact hpb
  change ‖cycleReturnMatrix p δ-1-δ • (orbitC α-(1/2:ℝ) • orbitC β)‖ ≤ _
  unfold cycleReturnMatrix
  change ‖harmonicMatrix b^(2*p)*harmonicMatrix a^p-1-
    δ • (orbitC α-(1/2:ℝ) • orbitC β)‖ ≤ _
  rw [harmonicMatrix_pow b hsB,harmonicMatrix_pow a hsA,hpa,hp₂]
  have hcosB : Real.cos (Real.pi-δ/2) = -Real.cos (δ/2) := by
    simp [Real.cos_sub]
  have hsinB : Real.sin (Real.pi-δ/2) = Real.sin (δ/2) := by
    simp [Real.sin_sub]
  have hcosA : Real.cos (Real.pi+δ) = -Real.cos δ := by
    simp [Real.cos_add]
  have hsinA : Real.sin (Real.pi+δ) = -Real.sin δ := by
    simp [Real.sin_add]
  rw [hcosB,hsinB,hcosA,hsinA,neg_smul (Real.sin δ) (orbitC a),← sub_eq_add_neg]
  exact orbit_return_remainder_of_bounds (orbitC a) (orbitC b) (orbitC α) (orbitC β)
    hp₇ hδ hδp hCa hCb hda hdb hac

end BreakingResonance

#print axioms BreakingResonance.cycleReturnMatrix_det
#print axioms BreakingResonance.cycleReturn_remainder
