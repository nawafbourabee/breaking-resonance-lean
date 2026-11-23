import BreakingResonance.LowerReturnMatrix

noncomputable section

open Matrix
open scoped Matrix Matrix.Norms.Operator

namespace BreakingResonance

def coneExpansionMatrix (c : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![-(1+c),-1;1,1+c]

def orbitPair (v : Fin 2 → ℝ) : ℝ×ℝ := (v 0,v 1)

theorem orbitPair_vector (z : ℝ×ℝ) : orbitPair (orbitVector z) = z := rfl

private theorem coneVector_norm_le {z : ℝ×ℝ} (hz : returnCone z) :
    ‖orbitVector z‖ ≤ 4*z.1 := by
  obtain ⟨hx,hy₁,hy₂⟩ := hz
  apply (pi_norm_le_iff_of_nonneg (show 0 ≤ 4*z.1 by positivity)).mpr
  intro i
  fin_cases i
  · change ‖z.1‖ ≤ _
    rw [Real.norm_eq_abs,abs_of_pos hx]
    linarith
  · change ‖z.2‖ ≤ _
    rw [Real.norm_eq_abs,abs_of_nonpos (by linarith only [hy₂,hx])]
    linarith only [hy₁]

theorem cone_of_boundary_slopes (M : Matrix (Fin 2) (Fin 2) ℝ) (hdet : M.det = 1)
    (hpos : ∀ s ∈ Set.Icc (-4:ℝ) (-3), 0 < M 0 0+M 0 1*s)
    (hlo : -4*(M 0 0+M 0 1*(-4)) ≤ M 1 0+M 1 1*(-4))
    (hhi : M 1 0+M 1 1*(-3) ≤ -3*(M 0 0+M 0 1*(-3)))
    {z : ℝ×ℝ} (hz : returnCone z) :
    returnCone (orbitPair (M *ᵥ orbitVector z)) := by
  obtain ⟨hx,hy₁,hy₂⟩ := hz
  let s := z.2/z.1
  have hs : s ∈ Set.Icc (-4:ℝ) (-3) :=
    ⟨(le_div_iff₀ hx).mpr hy₁,(div_le_iff₀ hx).mpr hy₂⟩
  let f := fun r : ℝ => M 0 0+M 0 1*r
  let g := fun r : ℝ => M 1 0+M 1 1*r
  have hmono : MonotoneOn (fun r => g r/f r) (Set.Icc (-4:ℝ) (-3)) := by
    intro u hu v hv huv
    apply (div_le_div_iff₀ (hpos u hu) (hpos v hv)).mpr
    have h : g v*f u-g u*f v = (v-u)*(M 0 0*M 1 1-M 0 1*M 1 0) := by
      dsimp [f,g]; ring
    rw [← Matrix.det_fin_two,hdet,mul_one] at h
    linarith only [h,huv]
  have hp := hpos s hs
  have h4 : (-4:ℝ) ∈ Set.Icc (-4:ℝ) (-3) := by constructor <;> norm_num
  have h3 : (-3:ℝ) ∈ Set.Icc (-4:ℝ) (-3) := by constructor <;> norm_num
  have hl : -4*f s ≤ g s := (le_div_iff₀ hp).mp
    (((le_div_iff₀ (hpos (-4) h4)).mpr hlo).trans (hmono h4 hs hs.1))
  have hu : g s ≤ -3*f s := (div_le_iff₀ hp).mp
    ((hmono hs h3 hs.2).trans ((div_le_iff₀ (hpos (-3) h3)).mpr hhi))
  have hy : z.1*s = z.2 := by dsimp [s]; field_simp
  have hpair : orbitPair (M *ᵥ orbitVector z) = (z.1*f s,z.1*g s) := by
    apply Prod.ext
    · simp [orbitPair,orbitVector,Matrix.mulVec,dotProduct,Fin.sum_univ_two,f]
      linear_combination -(M 0 1)*hy
    · simp [orbitPair,orbitVector,Matrix.mulVec,dotProduct,Fin.sum_univ_two,g]
      linear_combination -(M 1 1)*hy
  rw [hpair]
  exact ⟨mul_pos hx hp,
    by nlinarith only [mul_le_mul_of_nonneg_left hl hx.le],
    by nlinarith only [mul_le_mul_of_nonneg_left hu hx.le]⟩

set_option maxHeartbeats 600000 in
/-- The two boundary checks and positivity throughout the cone imply
invariance. The coordinate lower bound retains the factor in Lemma 7.1. -/
theorem expandedCone_of_small_remainder {M : Matrix (Fin 2) (Fin 2) ℝ}
    {t c : ℝ} (ht : 0 < t) (hc₀ : 4/5 ≤ c) (hc₁ : c ≤ 1)
    (hdet : M.det = 1)
    (hE : ‖M-1-t • coneExpansionMatrix c‖ ≤ t/20)
    {z : ℝ×ℝ} (hz : returnCone z) :
    returnCone (orbitPair (M *ᵥ orbitVector z)) ∧
      (1+4*t/5)*z.1 ≤ (M *ᵥ orbitVector z) 0 := by
  let E := M-1-t • coneExpansionMatrix c
  have hM : M = 1+t • coneExpansionMatrix c+E := by dsimp [E]; module
  have herr (w : ℝ×ℝ) (hw : returnCone w) (i : Fin 2) :
      |(E *ᵥ orbitVector w) i| ≤ t*w.1/5 := by
    rw [← Real.norm_eq_abs]
    refine (norm_le_pi_norm (E *ᵥ orbitVector w) i).trans
      ((Matrix.linfty_opNorm_mulVec E (orbitVector w)).trans ?_)
    have hx : 0 < w.1 := hw.1
    have h := mul_le_mul hE (coneVector_norm_le hw) (norm_nonneg _) (by positivity)
    nlinarith only [h]
  have h₀ (w : ℝ×ℝ) :
      (M *ᵥ orbitVector w) 0 =
        w.1+t*(-(1+c)*w.1-w.2)+(E *ᵥ orbitVector w) 0 := by
    simp [hM,coneExpansionMatrix,orbitVector,
      Matrix.mulVec,dotProduct,Fin.sum_univ_two,Matrix.one_apply]
    ring
  have h₁ (w : ℝ×ℝ) :
      (M *ᵥ orbitVector w) 1 =
        w.2+t*(w.1+(1+c)*w.2)+(E *ᵥ orbitVector w) 1 := by
    simp [hM,coneExpansionMatrix,orbitVector,
      Matrix.mulVec,dotProduct,Fin.sum_univ_two,Matrix.one_apply]
    ring
  have hcoord (w : ℝ×ℝ) (hw : returnCone w) :
      (1+4*t/5)*w.1 ≤ (M *ᵥ orbitVector w) 0 := by
    rw [h₀]
    have h := (abs_le.mp (herr w hw 0)).1
    have h' := mul_le_mul_of_nonneg_right hc₁ hw.1.le
    have h'' := mul_le_mul_of_nonneg_left
      (show w.1 ≤ -(1+c)*w.1-w.2 by linarith only [h',hw.2.2]) ht.le
    linarith only [h,h'']
  have hpos (s : ℝ) (hs : s ∈ Set.Icc (-4:ℝ) (-3)) :
      0 < M 0 0+M 0 1*s := by
    have h := hcoord (1,s) ⟨by norm_num,by simpa using hs.1,by simpa using hs.2⟩
    simp [orbitVector,Matrix.mulVec,dotProduct,Fin.sum_univ_two] at h
    linarith only [h,ht]
  have hlo : -4*(M 0 0+M 0 1*(-4)) ≤ M 1 0+M 1 1*(-4) := by
    let w : ℝ×ℝ := (1,-4)
    have hw : returnCone w := by norm_num [returnCone,w]
    have h : -4*(M *ᵥ orbitVector w) 0 ≤ (M *ᵥ orbitVector w) 1 := by
      rw [h₀,h₁]
      have he₀ := (abs_le.mp (herr w hw 0)).1
      have he₁ := (abs_le.mp (herr w hw 1)).1
      have hm := mul_le_mul_of_nonneg_left hc₁ ht.le
      dsimp [w] at he₀ he₁ ⊢
      nlinarith only [he₀,he₁,hm]
    simpa [w,orbitVector,Matrix.mulVec,dotProduct,Fin.sum_univ_two] using h
  have hhi : M 1 0+M 1 1*(-3) ≤ -3*(M 0 0+M 0 1*(-3)) := by
    let w : ℝ×ℝ := (1,-3)
    have hw : returnCone w := by norm_num [returnCone,w]
    have h : (M *ᵥ orbitVector w) 1 ≤ -3*(M *ᵥ orbitVector w) 0 := by
      rw [h₀,h₁]
      have he₀ := (abs_le.mp (herr w hw 0)).2
      have he₁ := (abs_le.mp (herr w hw 1)).2
      have hm := mul_le_mul_of_nonneg_left hc₀ ht.le
      dsimp [w] at he₀ he₁ ⊢
      nlinarith only [he₀,he₁,hm]
    simpa [w,orbitVector,Matrix.mulVec,dotProduct,Fin.sum_univ_two] using h
  exact ⟨cone_of_boundary_slopes M hdet hpos hlo hhi hz,hcoord z hz⟩

end BreakingResonance

#print axioms BreakingResonance.cone_of_boundary_slopes
#print axioms BreakingResonance.expandedCone_of_small_remainder
