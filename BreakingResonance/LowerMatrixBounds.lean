import BreakingResonance.LowerReturnMatrix

noncomputable section

open Matrix Set
open scoped Matrix Matrix.Norms.Operator

namespace BreakingResonance

theorem matrixTwo_norm (M : Matrix (Fin 2) (Fin 2) ℝ) :
    ‖M‖ = max (|M 0 0|+|M 0 1|) (|M 1 0|+|M 1 1|) := by
  rw [Matrix.linfty_opNorm_def]
  simp_rw [Fin.sum_univ_two]
  rw [Finset.univ_fin2]
  simp [Real.norm_eq_abs]

theorem cos_half_quotient {θ : ℝ} (hθ : 0 < θ) (hπ : θ < Real.pi) :
    (1+Real.cos θ)/Real.sin θ = Real.cos (θ/2)/Real.sin (θ/2) ∧
      (1-Real.cos θ)/Real.sin θ = Real.sin (θ/2)/Real.cos (θ/2) := by
  have hs : Real.sin (θ/2) ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith)).ne'
  have hc : Real.cos (θ/2) ≠ 0 := (Real.cos_pos_of_mem_Ioo
    (show θ/2 ∈ Ioo (-(Real.pi/2)) (Real.pi/2) from ⟨by linarith,by linarith⟩)).ne'
  have hsa : Real.sin θ = 2*Real.sin (θ/2)*Real.cos (θ/2) := by
    conv_lhs => rw [show θ = 2*(θ/2) by ring,Real.sin_two_mul]
  have hco : Real.cos θ = Real.cos (θ/2)^2-Real.sin (θ/2)^2 := by
    conv_lhs => rw [show θ = 2*(θ/2) by ring,Real.cos_two_mul']
  rw [hsa,hco]
  have hplus : 1+(Real.cos (θ/2)^2-Real.sin (θ/2)^2) = 2*Real.cos (θ/2)^2 := by
    nlinarith only [Real.sin_sq_add_cos_sq (θ/2)]
  have hminus : 1-(Real.cos (θ/2)^2-Real.sin (θ/2)^2) = 2*Real.sin (θ/2)^2 := by
    nlinarith only [Real.sin_sq_add_cos_sq (θ/2)]
  rw [hplus,hminus]
  constructor <;> field_simp [hs,hc] <;> ring

theorem orbitC_norm {θ : ℝ} (hθ : 0 < θ) (hπ : θ < Real.pi/2) :
    ‖orbitC θ‖ = (1+Real.cos θ)/Real.sin θ := by
  have hs := Real.sin_pos_of_pos_of_lt_pi hθ (by linarith only [hπ,Real.pi_pos])
  have hc := Real.cos_pos_of_mem_Ioo (show θ ∈ Ioo (-(Real.pi/2)) (Real.pi/2) from
    ⟨by linarith only [hθ,Real.pi_pos],hπ⟩)
  rw [matrixTwo_norm]
  simp [orbitC,abs_div,abs_of_pos hs,abs_of_pos hc,add_comm]
  ring

theorem orbitC_norm_le {θ : ℝ} (hθ : 0 < θ) (hπ : θ < Real.pi/2) :
    ‖orbitC θ‖ ≤ 2/θ := by
  rw [orbitC_norm hθ hπ,(cos_half_quotient hθ (by linarith only [hπ,Real.pi_pos])).1]
  have hco := Real.cos_pos_of_mem_Ioo (show θ/2 ∈ Ioo (-(Real.pi/2)) (Real.pi/2) from
    ⟨by linarith only [hθ,Real.pi_pos],by linarith only [hπ,Real.pi_pos]⟩)
  have hsi := Real.sin_pos_of_pos_of_lt_pi (show 0 < θ/2 by positivity)
    (by linarith only [hπ,Real.pi_pos])
  have ht := Real.le_tan (show 0 ≤ θ/2 by positivity) (by linarith only [hπ,Real.pi_pos])
  rw [Real.tan_eq_sin_div_cos] at ht
  have hh := (le_div_iff₀ hco).mp ht
  apply (div_le_div_iff₀ hsi hθ).mpr
  nlinarith only [hh]

/-- A difference of the C matrices gives the difference of two cotangents.
The last bound is the direct trigonometric version of the derivative estimate. -/
theorem orbitC_difference {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) (hv : v < Real.pi/2) :
    ‖orbitC v-orbitC u‖ ≤ Real.pi^2*(v-u)/(2*u*v) := by
  have hv₀ := hu.trans_le huv
  have hsU := Real.sin_pos_of_pos_of_lt_pi hu (by linarith only [huv,hv,Real.pi_pos])
  have hsV := Real.sin_pos_of_pos_of_lt_pi hv₀ (by linarith only [hv,Real.pi_pos])
  have huI : u ∈ Icc (-(Real.pi/2)) (Real.pi/2) :=
    ⟨by linarith only [hu,Real.pi_pos],huv.trans hv.le⟩
  have hvI : v ∈ Icc (-(Real.pi/2)) (Real.pi/2) :=
    ⟨huI.1.trans huv,hv.le⟩
  have hsm := Real.strictMonoOn_sin.monotoneOn huI hvI huv
  have hcm := Real.strictAntiOn_cos.antitoneOn
    (show u ∈ Icc 0 Real.pi from ⟨hu.le,by linarith only [huv,hv,Real.pi_pos]⟩)
    (show v ∈ Icc 0 Real.pi from ⟨hv₀.le,by linarith only [hv,Real.pi_pos]⟩) huv
  have hcV := Real.cos_pos_of_mem_Ioo (show v ∈ Ioo (-(Real.pi/2)) (Real.pi/2) from
    ⟨by linarith only [hv₀,Real.pi_pos],hv⟩)
  have hratio : Real.cos v/Real.sin v ≤ Real.cos u/Real.sin u :=
    (div_le_div_of_nonneg_left hcV.le hsU hsm).trans
      (div_le_div_of_nonneg_right hcm hsU.le)
  have hrecip : 1/Real.sin v ≤ 1/Real.sin u := one_div_le_one_div_of_le hsU hsm
  have hnorm : ‖orbitC v-orbitC u‖ =
      (1+Real.cos u)/Real.sin u-(1+Real.cos v)/Real.sin v := by
    rw [matrixTwo_norm]
    simp only [Matrix.sub_apply]
    simp only [orbitC, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.vecHead, Matrix.cons_val_fin_one]
    have h₁ : |Real.cos v/Real.sin v-Real.cos u/Real.sin u| =
        Real.cos u/Real.sin u-Real.cos v/Real.sin v := by
      rw [abs_of_nonpos (sub_nonpos.mpr hratio)]
      ring
    have h₂ : |-1/Real.sin v-(-1/Real.sin u)| = 1/Real.sin u-1/Real.sin v := by
      rw [show -1/Real.sin v-(-1/Real.sin u) = 1/Real.sin u-1/Real.sin v by ring,
        abs_of_nonneg (sub_nonneg.mpr hrecip)]
    have h₃ : |1/Real.sin v-1/Real.sin u| = 1/Real.sin u-1/Real.sin v := by
      rw [abs_of_nonpos (sub_nonpos.mpr hrecip)]
      ring
    have h₄ : |-Real.cos v/Real.sin v-(-Real.cos u/Real.sin u)| =
        Real.cos u/Real.sin u-Real.cos v/Real.sin v := by
      rw [show -Real.cos v/Real.sin v-(-Real.cos u/Real.sin u) =
        Real.cos u/Real.sin u-Real.cos v/Real.sin v by ring,abs_of_nonneg (sub_nonneg.mpr hratio)]
    rw [h₁,h₂,h₃,h₄,show 1/Real.sin u-1/Real.sin v+
      (Real.cos u/Real.sin u-Real.cos v/Real.sin v) =
      Real.cos u/Real.sin u-Real.cos v/Real.sin v+(1/Real.sin u-1/Real.sin v) by ring,
      max_self]
    ring
  rw [hnorm,
    (cos_half_quotient hu (by linarith only [huv,hv,Real.pi_pos])).1,
    (cos_half_quotient hv₀ (by linarith only [hv,Real.pi_pos])).1]
  have hu₂ : 0 < Real.sin (u/2) := Real.sin_pos_of_pos_of_lt_pi (by positivity)
    (by linarith only [huv,hv,Real.pi_pos])
  have hv₂ : 0 < Real.sin (v/2) := Real.sin_pos_of_pos_of_lt_pi (by positivity)
    (by linarith only [hv,Real.pi_pos])
  have he : Real.cos (u/2)/Real.sin (u/2)-Real.cos (v/2)/Real.sin (v/2) =
      Real.sin ((v-u)/2)/(Real.sin (u/2)*Real.sin (v/2)) := by
    rw [show (v-u)/2 = v/2-u/2 by ring,Real.sin_sub]
    field_simp [hu₂.ne',hv₂.ne']
  rw [he]
  have hlow : (u/Real.pi)*(v/Real.pi) ≤ Real.sin (u/2)*Real.sin (v/2) := by
    have h₁ := Real.mul_le_sin (show 0 ≤ u/2 by positivity)
      (by linarith only [huv,hv,Real.pi_pos])
    have h₂ := Real.mul_le_sin (show 0 ≤ v/2 by positivity)
      (by linarith only [hv,Real.pi_pos])
    rw [show 2/Real.pi*(u/2) = u/Real.pi by ring] at h₁
    rw [show 2/Real.pi*(v/2) = v/Real.pi by ring] at h₂
    exact mul_le_mul h₁ h₂ (by positivity) hu₂.le
  calc
    _ ≤ ((v-u)/2)/(Real.sin (u/2)*Real.sin (v/2)) :=
      div_le_div_of_nonneg_right (Real.sin_le (by linarith only [huv])) (by positivity)
    _ ≤ ((v-u)/2)/((u/Real.pi)*(v/Real.pi)) :=
      div_le_div_of_nonneg_left (by linarith only [huv]) (by positivity) hlow
    _ = _ := by field_simp [Real.pi_pos.ne',hu.ne',hv₀.ne']

end BreakingResonance

#print axioms BreakingResonance.orbitC_norm_le
#print axioms BreakingResonance.orbitC_difference
