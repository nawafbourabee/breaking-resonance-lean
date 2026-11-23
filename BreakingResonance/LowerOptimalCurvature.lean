import BreakingResonance.LowerConstructedTarget

noncomputable section

open Set

namespace BreakingResonance

theorem lowerPotential_auxiliary_axis (κ h δ : ℝ) (j : Fin 2) (x : ℝ) :
    lowerPotential κ h δ (PiLp.single 2 (Sum.inr j) x) = lowerAuxCurvature κ j*x^2/2 := by
  unfold lowerPotential separablePotential
  rw [Finset.sum_eq_single (Sum.inr j)]
  · simp [PiLp.single_apply,lowerCurvatureNeg,lowerCurvaturePos,fastPotential]
  · intro i _ hi
    simp [PiLp.single_apply,Ne.symm hi,fastPotential]
  · simp

theorem lowerForce_auxiliary_axis (κ h δ : ℝ) (j : Fin 2) (x : ℝ) :
    lowerForce κ h δ (PiLp.single 2 (Sum.inr j) x) =
      PiLp.single 2 (Sum.inr j) (lowerAuxCurvature κ j*x) := by
  ext i
  by_cases hi : i = Sum.inr j
  · subst i
    simp [lowerForce,separableForce,PiLp.single_apply,lowerCurvatureNeg,lowerCurvaturePos,fastGradient]
  · simp [lowerForce,separableForce,PiLp.single_apply,hi,Ne.symm hi,fastGradient]

theorem lowerForce_zero (κ h δ : ℝ) :
    lowerForce κ h δ 0 = 0 := by
  ext i
  simp [lowerForce,separableForce,fastGradient]

theorem lowerPotential_zero (κ h δ : ℝ) :
    lowerPotential κ h δ 0 = 0 := by
  simp [lowerPotential,separablePotential,fastPotential]

theorem lowerForce_optimal_lipschitz (κ h δ : ℝ) (L : NNReal)
    (hL : LipschitzWith L (lowerForce κ h δ)) :
    1 ≤ (L:ℝ) := by
  let z : EuclideanSpace ℝ (LowerCoordinate κ) := PiLp.single 2 (Sum.inr (0:Fin 2)) 1
  have hf : lowerForce κ h δ z = z := by
    dsimp only [z]
    rw [lowerForce_auxiliary_axis]
    simp [lowerAuxCurvature]
  have he := (lipschitzWith_iff_dist_le_mul.mp hL) z 0
  rw [hf,lowerForce_zero,dist_zero_right] at he
  simpa [z,PiLp.norm_single] using he

theorem lowerPotential_optimal_strongConvex (κ h δ m : ℝ)
    (hm : StrongConvexOn univ m (lowerPotential κ h δ)) :
    m ≤ κ⁻¹ := by
  let i : LowerCoordinate κ := Sum.inr (1:Fin 2)
  let x : EuclideanSpace ℝ (LowerCoordinate κ) := PiLp.single 2 i (-1)
  let y : EuclideanSpace ℝ (LowerCoordinate κ) := PiLp.single 2 i 1
  have hsConv : UniformConvexOn univ (fun r => m/2*r^2) (lowerPotential κ h δ) := hm
  obtain ⟨_,hStrong⟩ := hsConv
  have hmid := @hStrong x (mem_univ x) y (mem_univ y) ((1:ℝ)/2) ((1:ℝ)/2)
    (by norm_num) (by norm_num) (by norm_num)
  change lowerPotential κ h δ ((1/2:ℝ) • x+(1/2:ℝ) • y) ≤
    (1/2)*lowerPotential κ h δ x+(1/2)*lowerPotential κ h δ y-
      (1/2)*(1/2)*(m/2*‖x-y‖^2) at hmid
  have he : (1/2:ℝ) • x+(1/2:ℝ) • y = 0 := by
    ext j
    simp only [x,y,PiLp.add_apply,PiLp.smul_apply,PiLp.single_apply,PiLp.zero_apply,smul_eq_mul]
    split_ifs <;> norm_num
  have hs : ‖x-y‖ = 2 := by
    dsimp [x,y]
    rw [← PiLp.single_sub,PiLp.norm_single]
    norm_num
  rw [he,hs,lowerPotential_zero] at hmid
  dsimp only [x,y,i] at hmid
  rw [lowerPotential_auxiliary_axis,lowerPotential_auxiliary_axis] at hmid
  have hj : lowerAuxCurvature κ (1:Fin 2) = κ⁻¹ := by norm_num [lowerAuxCurvature]
  rw [hj] at hmid
  linarith only [hmid]

end BreakingResonance

#print axioms BreakingResonance.lowerForce_optimal_lipschitz
#print axioms BreakingResonance.lowerPotential_optimal_strongConvex
