import BreakingResonance.LowerMatrixBounds

noncomputable section

open Matrix Set
open scoped Matrix Matrix.Norms.Operator

namespace BreakingResonance

theorem orbitC_product_norm {a b : ℝ} (hb : 0 < b) (hba : b ≤ a)
    (ha : a ≤ Real.pi/3) :
    ‖orbitC b * orbitC a‖ =
      ((1-Real.cos a)/Real.sin a)*((1+Real.cos b)/Real.sin b) := by
  have ha₀ := hb.trans_le hba
  have haπ : a < Real.pi/2 := by linarith only [ha,Real.pi_pos]
  have hbπ := hba.trans_lt haπ
  have hsa := Real.sin_pos_of_pos_of_lt_pi ha₀ (by linarith only [ha,Real.pi_pos])
  have hsb := Real.sin_pos_of_pos_of_lt_pi hb (by linarith only [hba,ha,Real.pi_pos])
  have hm := Real.strictAntiOn_cos.antitoneOn
    (show b ∈ Icc 0 Real.pi from ⟨hb.le,by linarith only [hba,ha,Real.pi_pos]⟩)
    (show a ∈ Icc 0 Real.pi from ⟨ha₀.le,by linarith only [ha,Real.pi_pos]⟩) hba
  have hca := Real.cos_pos_of_mem_Ioo (show a ∈ Ioo (-(Real.pi/2)) (Real.pi/2) from
    ⟨by linarith only [ha₀,Real.pi_pos],haπ⟩)
  have hdiag : Real.cos a*Real.cos b ≤ 1 := by
    have h := mul_le_mul (Real.cos_le_one a) (Real.cos_le_one b) (hca.le.trans hm) zero_le_one
    simpa using h
  let d := (Real.cos a*Real.cos b-1)/(Real.sin a*Real.sin b)
  let e := (Real.cos a-Real.cos b)/(Real.sin a*Real.sin b)
  have hd : d ≤ 0 := div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hdiag) (by positivity)
  have he : e ≤ 0 := div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hm) (by positivity)
  have hproduct : orbitC b * orbitC a = !![d,e;e,d] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [orbitC, Matrix.mul_apply, Fin.sum_univ_two, d,e] <;>
      field_simp [hsa.ne',hsb.ne'] <;> ring
  rw [hproduct,matrixTwo_norm]
  simp only [Matrix.of_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,
    abs_of_nonpos hd, abs_of_nonpos he, add_comm (-d) (-e),max_self]
  dsimp [d,e]
  ring

theorem orbitC_product_norm_le_four {a b : ℝ} (hb : 0 < b) (hba : b ≤ a)
    (ha : a ≤ Real.pi/3) (hs : a ≤ 3*b) : ‖orbitC b * orbitC a‖ ≤ 4 := by
  have ha₀ := hb.trans_le hba
  have hπ := Real.pi_pos
  have hpi : a < Real.pi := by linarith only [ha,hπ]
  have hca : Real.sqrt 3/2 ≤ Real.cos (a/2) := by
    rw [← Real.cos_pi_div_six]
    exact Real.strictAntiOn_cos.antitoneOn
      (show a/2 ∈ Icc 0 Real.pi from ⟨by positivity,by linarith only [ha,hπ]⟩)
      (show Real.pi/6 ∈ Icc 0 Real.pi from ⟨by positivity,by linarith only [hπ]⟩)
      (by linarith only [ha])
  have hcp : 0 < Real.cos (a/2) := (by positivity : 0 < Real.sqrt 3/2).trans_le hca
  have hsa : 0 ≤ Real.sin (a/2) :=
    (Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith only [hpi,hπ])).le
  have htan : (1-Real.cos a)/Real.sin a ≤ a/Real.sqrt 3 := by
    rw [(cos_half_quotient ha₀ hpi).2]
    have he : (a/2)/(Real.sqrt 3/2) = a/Real.sqrt 3 := by ring
    rw [← he]
    exact (div_le_div_of_nonneg_right (Real.sin_le (by positivity)) hcp.le).trans
      (div_le_div_of_nonneg_left (by positivity) (by positivity) hca)
  have hcot : (1+Real.cos b)/Real.sin b ≤ 2/b := by
    have hbl : b < Real.pi/2 := by linarith only [ha,hba,hπ]
    rw [← orbitC_norm hb hbl]
    exact orbitC_norm_le hb hbl
  have hsqr : 6 ≤ 4*Real.sqrt 3 := by
    nlinarith only [Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num),
      Real.sqrt_nonneg (3:ℝ)]
  rw [orbitC_product_norm hb hba ha]
  calc
    _ ≤ (a/Real.sqrt 3)*(2/b) := mul_le_mul htan hcot
      (by
        have hbl : b < Real.pi/2 := by linarith only [ha,hba,hπ]
        rw [← orbitC_norm hb hbl]
        exact norm_nonneg _)
      (by positivity)
    _ ≤ 4 := by
      rw [div_mul_div_comm]
      apply (div_le_iff₀ (by positivity : 0 < Real.sqrt 3*b)).mpr
      have hsc := mul_le_mul_of_nonneg_right hsqr hb.le
      nlinarith only [hsc,hs]

theorem one_sub_cos_le_half_square {t : ℝ} (ht : 0 ≤ t) :
    1-Real.cos t ≤ t^2/2 := by
  have hcos : Real.cos t = Real.cos (t/2)^2-Real.sin (t/2)^2 := by
    conv_lhs => rw [show t = 2*(t/2) by ring,Real.cos_two_mul']
  have ht' := (sq_le_sq₀ (abs_nonneg (Real.sin (t/2))) (by positivity : 0 ≤ t/2)).mpr
    (by simpa only [abs_of_nonneg (show 0 ≤ t/2 by positivity)] using
      (Real.abs_sin_le_abs (x := t/2)))
  rw [sq_abs] at ht'
  rw [hcos]
  nlinarith only [ht',Real.sin_sq_add_cos_sq (t/2)]

end BreakingResonance

#print axioms BreakingResonance.orbitC_product_norm_le_four
#print axioms BreakingResonance.one_sub_cos_le_half_square
