import BreakingResonance.LowerOrbit

noncomputable section

open PersistencePays

namespace BreakingResonance

def orbitQuadratic (h θ : ℝ) (z : ℝ×ℝ) : ℝ :=
  (z.1^2+z.2^2-2*Real.cos θ*z.1*z.2)/h^2

def asymmetricPotential (h : ℝ) (p : ℕ) (δ : ℝ) : ℝ → ℝ :=
  fastPotential (curvatureForAngle h (fastAngleNeg p δ))
    (curvatureForAngle h (fastAnglePos p δ))

theorem orbitQuadratic_step (h θ : ℝ) (z : ℝ×ℝ) :
    orbitQuadratic h θ (harmonicStep θ z) = orbitQuadratic h θ z := by
  unfold orbitQuadratic harmonicStep
  congr 1
  ring

theorem orbitQuadratic_iterate (h θ : ℝ) (z : ℝ×ℝ) (n : ℕ) :
    orbitQuadratic h θ ((harmonicStep θ)^[n] z) = orbitQuadratic h θ z := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply',orbitQuadratic_step,ih]

theorem curvatureForAngle_cos {h θ : ℝ} (hh : h ≠ 0) :
    1-h^2/2*curvatureForAngle h θ = Real.cos θ := by
  have hc : Real.cos θ = Real.cos (θ/2)^2-Real.sin (θ/2)^2 := by
    conv_lhs => rw [show θ = 2*(θ/2) by ring,Real.cos_two_mul']
  rw [hc,curvatureForAngle]
  field_simp [hh]
  nlinarith only [Real.sin_sq_add_cos_sq (θ/2)]

theorem fast_energy_coordinates {h : ℝ} (hh : h ≠ 0) (a b : ℝ) (z : ℝ×ℝ) :
    let θ := if 0 ≤ z.1 then a else b
    let κθ := curvatureForAngle h θ
    let g := fastGradient (curvatureForAngle h b) (curvatureForAngle h a)
    let U := fastPotential (curvatureForAngle h b) (curvatureForAngle h a)
    consecutivePositions g h z = (z.1,Real.cos θ*z.1-h*z.2) ∧
      phaseEnergy U z = (z.2^2+κθ*z.1^2)/2 ∧
      orbitQuadratic h θ (consecutivePositions g h z) =
        z.2^2+κθ*(1-h^2*κθ/4)*z.1^2 := by
  let θ := if 0 ≤ z.1 then a else b
  let κθ := curvatureForAngle h θ
  let g := fastGradient (curvatureForAngle h b) (curvatureForAngle h a)
  let U := fastPotential (curvatureForAngle h b) (curvatureForAngle h a)
  have hg : g z.1 = κθ*z.1 := by
    by_cases hz : 0 ≤ z.1 <;> simp [g,κθ,θ,fastGradient,hz]
  have hU : U z.1 = κθ*z.1^2/2 := by
    by_cases hz : 0 ≤ z.1 <;> simp [U,κθ,θ,fastPotential,hz]
  have hc : 1-h^2/2*κθ = Real.cos θ := curvatureForAngle_cos hh
  have hp : consecutivePositions g h z = (z.1,Real.cos θ*z.1-h*z.2) := by
    rw [← hc]
    simp [consecutivePositions,hg]
    ring
  refine ⟨hp,?_,?_⟩
  · change phaseEnergy U z = (z.2^2+κθ*z.1^2)/2
    rw [phaseEnergy,hU,real_inner_self_eq_norm_sq,Real.norm_eq_abs,sq_abs]
    ring
  · rw [hp,orbitQuadratic,← hc]
    field_simp [hh]
    ring

theorem fast_energy_sandwich {h : ℝ} (hh : h ≠ 0) (a b : ℝ) (z : ℝ×ℝ)
    (hpos : h^2*curvatureForAngle h a ≤ 1) (hneg : h^2*curvatureForAngle h b ≤ 1) :
    let θ := if 0 ≤ z.1 then a else b
    let κθ := curvatureForAngle h θ
    let g := fastGradient (curvatureForAngle h b) (curvatureForAngle h a)
    let U := fastPotential (curvatureForAngle h b) (curvatureForAngle h a)
    let q := orbitQuadratic h θ (consecutivePositions g h z)
    q/2 ≤ phaseEnergy U z ∧ phaseEnergy U z ≤ q/(2*(1-h^2*κθ/4)) := by
  let θ := if 0 ≤ z.1 then a else b
  let κθ := curvatureForAngle h θ
  let g := fastGradient (curvatureForAngle h b) (curvatureForAngle h a)
  let U := fastPotential (curvatureForAngle h b) (curvatureForAngle h a)
  obtain ⟨_,hH,hQ⟩ := fast_energy_coordinates hh a b z
  have hl : h^2*κθ ≤ 1 := by by_cases hz : 0 ≤ z.1 <;> simpa [κθ,θ,hz]
  have hκθ : 0 ≤ κθ := by unfold κθ curvatureForAngle; positivity
  have hi : 0 ≤ h^2*κθ/4 := by positivity
  have hc : 0 < 2*(1-h^2*κθ/4) := by linarith only [hl]
  change orbitQuadratic h θ (consecutivePositions g h z)/2 ≤ phaseEnergy U z ∧ _
  rw [hH,hQ]
  refine ⟨?_,(le_div_iff₀ hc).mpr ?_⟩
  · nlinarith only [mul_nonneg hi (show 0 ≤ κθ*z.1^2 by positivity)]
  · nlinarith only [mul_nonneg hi (sq_nonneg z.2)]

theorem orbitQuadratic_cone_lower {h a : ℝ} (ha : 0 ≤ Real.cos a)
    {z : ℝ×ℝ} (hz : returnCone z) : 10*(z.1/h)^2 ≤ orbitQuadratic h a z := by
  obtain ⟨hx,_,hy⟩ := hz
  have hy₀ : 0 ≤ -z.2 := by linarith only [hx,hy]
  have he : 10*(z.1/h)^2 = (10*z.1^2)/h^2 := by ring
  rw [he,orbitQuadratic]
  apply div_le_div_of_nonneg_right _ (sq_nonneg h)
  have hs := (sq_le_sq₀ (show 0 ≤ 3*z.1 by positivity) hy₀).mpr
    (show 3*z.1 ≤ -z.2 by linarith only [hy])
  have hpos := mul_nonneg (mul_nonneg ha hx.le) hy₀
  nlinarith only [hs,hpos]

theorem orbitQuadratic_switch {h a b : ℝ} (ha : 0 ≤ Real.cos a)
    (hab : Real.cos a ≤ Real.cos b) {z : ℝ×ℝ} (hxy : z.1*z.2 ≤ 0) :
    orbitQuadratic h a z ≤ orbitQuadratic h b z ∧
      orbitQuadratic h b z ≤ 2*orbitQuadratic h a z := by
  have h₁ := mul_nonneg (sub_nonneg.mpr hab) (neg_nonneg.mpr hxy)
  have h₂ := mul_nonneg ha (neg_nonneg.mpr hxy)
  have h₃ := mul_nonneg (sub_nonneg.mpr (Real.cos_le_one b)) (neg_nonneg.mpr hxy)
  unfold orbitQuadratic
  rw [← mul_div_assoc]
  constructor <;> apply div_le_div_of_nonneg_right _ (sq_nonneg h)
  · nlinarith only [h₁]
  · nlinarith only [h₂,h₃,sq_nonneg (z.1+z.2)]

end BreakingResonance

#print axioms BreakingResonance.orbitQuadratic_iterate
#print axioms BreakingResonance.fast_energy_coordinates
#print axioms BreakingResonance.fast_energy_sandwich
#print axioms BreakingResonance.orbitQuadratic_cone_lower
#print axioms BreakingResonance.orbitQuadratic_switch
