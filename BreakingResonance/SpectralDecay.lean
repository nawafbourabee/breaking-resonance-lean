import BreakingResonance.MarkovL2

noncomputable section

open scoped InnerProductSpace RealInnerProductSpace

namespace BreakingResonance

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The norm-decay inequality for a symmetric contraction bounded below by `-1 + β`. -/
theorem spectralGap_decay (Q : H →L[ℝ] H) (hQ : Q.IsSymmetric)
    (hcon : ∀ f, ‖Q f‖ ≤ ‖f‖) {β : ℝ} (hβ : β ≤ 1)
    (hgap : ∀ f, (-1+β)*‖f‖^2 ≤ ⟪f,Q f⟫_ℝ) (f : H) :
    β*(‖f‖^2-⟪f,Q f⟫_ℝ) ≤ ‖f‖^2-‖Q f‖^2 := by
  let B : H →L[ℝ] H := Q + (1-β) • 1
  let k : ℝ := 2-β
  have hk : 0 < k := by dsimp [k]; linarith only [hβ]
  have hB_apply (x : H) : B x = Q x+(1-β) • x := rfl
  have hQ_symm (x y : H) : ⟪Q x,y⟫_ℝ = ⟪x,Q y⟫_ℝ := hQ x y
  have hB_symm (x y : H) : ⟪B x,y⟫_ℝ = ⟪x,B y⟫_ℝ := by
    simp only [hB_apply, inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right, hQ_symm]
  have hform (x : H) : ⟪B x,x⟫_ℝ = ⟪x,Q x⟫_ℝ+(1-β)*‖x‖^2 := by
    rw [hB_apply,inner_add_left,real_inner_smul_left,real_inner_self_eq_norm_sq,
      real_inner_comm x (Q x)]
  have hpos (x : H) : 0 ≤ ⟪B x,x⟫_ℝ := by
    rw [hform]
    linarith only [hgap x]
  have hup (x : H) : ⟪B x,x⟫_ℝ ≤ k*‖x‖^2 := by
    rw [hform]
    have hbound := real_inner_le_norm x (Q x)
    have hmult := mul_le_mul_of_nonneg_left (hcon x) (norm_nonneg x)
    dsimp [k]
    nlinarith only [hbound, hmult]
  have hcross : ⟪B (B f),f⟫_ℝ = ‖B f‖^2 := by
    rw [hB_symm, real_inner_self_eq_norm_sq]
  have htest := hpos (k • f-B f)
  rw [map_sub, map_smul, inner_sub_left, inner_sub_right, inner_sub_right,
    real_inner_smul_left, real_inner_smul_left, real_inner_smul_right, real_inner_smul_right,
    hcross, real_inner_self_eq_norm_sq] at htest
  have hscaled := hup (B f)
  have hnonneg : 0 ≤ k*(k*⟪B f,f⟫_ℝ-‖B f‖^2) := by nlinarith only [htest,hscaled]
  have hBbound : ‖B f‖^2 ≤ k*⟪B f,f⟫_ℝ := by
    linarith only [(nonneg_of_mul_nonneg_right hnonneg hk)]
  rw [hform] at hBbound
  have hnorm : ‖B f‖^2 = ‖Q f‖^2+2*(1-β)*⟪f,Q f⟫_ℝ+(1-β)^2*‖f‖^2 := by
    rw [hB_apply, ← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right,
      inner_add_right, real_inner_smul_left, real_inner_smul_left, real_inner_smul_right,
      real_inner_smul_right, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
      real_inner_comm (Q f) f]
    ring
  rw [hnorm] at hBbound
  dsimp [k] at hBbound
  nlinarith only [hBbound]

end BreakingResonance

#print axioms BreakingResonance.spectralGap_decay
