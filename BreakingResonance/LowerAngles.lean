import BreakingResonance.LowerPositionRecurrence
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

noncomputable section

namespace BreakingResonance

def cycleHalfLength (h : ℝ) : ℕ := Nat.ceil (2*Real.pi/h)

def fastAnglePos (p : ℕ) (δ : ℝ) : ℝ := (Real.pi+δ)/(p:ℝ)

def fastAngleNeg (p : ℕ) (δ : ℝ) : ℝ := (Real.pi-δ/2)/(2*(p:ℝ))

theorem cycleHalfLength_bounds {h : ℝ} (hh : 0 < h) (hh₁ : h ≤ 1) :
    let p := cycleHalfLength h
    7 ≤ p ∧ 2*Real.pi ≤ (p:ℝ)*h ∧ (p:ℝ)*h < 2*Real.pi+1 := by
  let p := cycleHalfLength h
  have hπ := Real.pi_pos
  have hl : 6 < 2*Real.pi/h := (lt_div_iff₀ hh).mpr (by
    linarith only [Real.pi_gt_three,hh₁])
  have hp : 7 ≤ p := Nat.add_one_le_ceil_iff.mpr hl
  have hph := (div_le_iff₀ hh).mp (Nat.le_ceil (2*Real.pi/h))
  have hup := (lt_div_iff₀ hh).mp (show (p:ℝ) < (2*Real.pi+h)/h from by
    rw [add_div,div_self hh.ne']
    exact Nat.ceil_lt_add_one (by positivity))
  exact ⟨hp,hph,hup.trans_le (by linarith only [hh₁])⟩

theorem fastAngle_bounds {p : ℕ} (hp : 7 ≤ p) {δ : ℝ} (hδ : 0 < δ)
    (hδ₁ : δ ≤ 1/(80*(p:ℝ)^2)) :
    let a := fastAnglePos p δ
    let b := fastAngleNeg p δ
    0 < b ∧ 3/(2*(p:ℝ)) ≤ b ∧ b < a ∧ a ≤ Real.pi/3 ∧ a ≤ 3*b ∧
      (p:ℝ)*a = Real.pi+δ ∧ (2*(p:ℝ))*b = Real.pi-δ/2 := by
  let a := fastAnglePos p δ
  let b := fastAngleNeg p δ
  have hp₁ : 7 ≤ (p:ℝ) := by exact_mod_cast hp
  have hpp : 0 < (p:ℝ) := by linarith
  have hδsmall : δ ≤ 1/80 := hδ₁.trans (by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    nlinarith only [hp₁,sq_nonneg ((p:ℝ)-7)])
  have hb₃ : 3/(2*(p:ℝ)) ≤ b := by
    dsimp [b,fastAngleNeg]
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith only [Real.pi_gt_d2,hδsmall]
  have hb₀ : 0 < b := (by positivity : 0 < 3/(2*(p:ℝ))).trans_le hb₃
  have hab : b < a := by
    apply (lt_div_iff₀ hpp).mpr
    change b*(p:ℝ) < Real.pi+δ
    have h : b*(p:ℝ) = (Real.pi-δ/2)/2 := by
      dsimp [b,fastAngleNeg]
      field_simp
    rw [h]
    linarith only [Real.pi_pos,hδ]
  have haπ : a ≤ Real.pi/3 := (div_le_iff₀ hpp).mpr (by
    have h := mul_le_mul_of_nonneg_right hp₁ Real.pi_pos.le
    nlinarith only [Real.pi_gt_three,h,hδsmall])
  have hab₃ : a ≤ 3*b := by
    have hb : (3*b)*(p:ℝ) = 3*(Real.pi-δ/2)/2 := by
      dsimp [b,fastAngleNeg]
      field_simp
    apply (div_le_iff₀ hpp).mpr
    rw [hb]
    linarith only [Real.pi_gt_three,hδsmall]
  refine ⟨hb₀,hb₃,hab,haπ,hab₃,?_,?_⟩
  · dsimp [a,fastAnglePos]; field_simp
  · dsimp [b,fastAngleNeg]; field_simp

/-- The curvatures of the asymmetric quadratic target, with the bounds
in Section 7.2. -/
theorem fastCurvature_bounds {h δ : ℝ} (hh : 0 < h) (hh₁ : h ≤ 1)
    (hδ : 0 < δ) (hδ₁ : δ ≤ 1/(80*(cycleHalfLength h:ℝ)^2)) :
    let p := cycleHalfLength h
    let a := fastAnglePos p δ
    let b := fastAngleNeg p δ
    1/16 ≤ curvatureForAngle h a ∧ curvatureForAngle h a < 1 ∧
      1/64 ≤ curvatureForAngle h b ∧ curvatureForAngle h b < curvatureForAngle h a := by
  let p := cycleHalfLength h
  let a := fastAnglePos p δ
  let b := fastAngleNeg p δ
  obtain ⟨hp,hph,hph'⟩ := cycleHalfLength_bounds hh hh₁
  have hp₁ : 7 ≤ (p:ℝ) := by exact_mod_cast hp
  have hpp : 0 < (p:ℝ) := by linarith
  obtain ⟨hb,hb₃,hba,haπ,_,hpa,hpb⟩ := fastAngle_bounds hp hδ hδ₁
  have ha : 0 < a := hb.trans hba
  have hbπ := hba.le.trans haπ
  have hπ := Real.pi_pos
  have hap : a/2 ≤ Real.pi/2 := by linarith only [haπ,hπ]
  have hbp : b/2 ≤ Real.pi/2 := by linarith only [hbπ,hπ]
  have hsa := Real.mul_le_sin (by positivity : 0 ≤ a/2) hap
  have hsb := Real.mul_le_sin (by positivity : 0 ≤ b/2) hbp
  have hπp : 0 < Real.pi*(p:ℝ) := mul_pos hπ hpp
  have hsinA : h/8 ≤ Real.sin (a/2) := by
    have h1 : 1/(p:ℝ) ≤ 2/Real.pi*(a/2) := by
      rw [show 2/Real.pi*(a/2) = a/Real.pi by ring]
      rw [div_le_div_iff₀ hpp hπ]
      have h := hpa
      linarith only [h,hδ]
    have h2 : h/8 ≤ 1/(p:ℝ) := by
      rw [div_le_div_iff₀ (by norm_num : (0:ℝ) < 8) hpp]
      linarith only [hph',Real.pi_lt_d2]
    exact h2.trans (h1.trans hsa)
  have hsinB : h/16 ≤ Real.sin (b/2) := by
    have h1 : 3/(2*(Real.pi*(p:ℝ))) ≤ 2/Real.pi*(b/2) := by
      have he₁ : (3/(2*(p:ℝ)))/Real.pi = 3/(2*(Real.pi*(p:ℝ))) := by
        field_simp [hπ.ne', hpp.ne']
      have he₂ : b/Real.pi = 2/Real.pi*(b/2) := by ring
      rw [← he₁,← he₂]
      exact div_le_div_of_nonneg_right hb₃ hπ.le
    have h2 : h/16 ≤ 3/(2*(Real.pi*(p:ℝ))) := by
      have he : Real.pi*((p:ℝ)*h) < 24 := by
        have h := mul_le_mul (show Real.pi ≤ 3.15 from Real.pi_lt_d2.le)
          (show (p:ℝ)*h ≤ 7.3 by linarith only [hph',Real.pi_lt_d2])
          (by positivity : 0 ≤ (p:ℝ)*h) (by norm_num : (0:ℝ) ≤ 3.15)
        linarith only [h]
      rw [div_le_div_iff₀ (by norm_num : (0:ℝ) < 16) (by positivity)]
      nlinarith only [he]
    exact h2.trans (h1.trans hsb)
  have hδsmall : δ ≤ 1/80 := hδ₁.trans (by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    nlinarith only [hp₁,sq_nonneg ((p:ℝ)-7)])
  have hah : a < h := by
    apply (div_lt_iff₀ hpp).mpr
    linarith only [hph,hδsmall,Real.pi_gt_three]
  have hupper : Real.sin (a/2) < h/2 := (Real.sin_le (by positivity)).trans_lt (by linarith)
  have hsm : Real.sin (b/2) < Real.sin (a/2) :=
    Real.strictMonoOn_sin (show b/2 ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) from ⟨by linarith,hbp⟩)
      (show a/2 ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) from ⟨by linarith,hap⟩) (by linarith)
  have hsA : 0 ≤ Real.sin (a/2) := (by positivity : 0 ≤ h/8).trans hsinA
  have hsB : 0 ≤ Real.sin (b/2) := (by positivity : 0 ≤ h/16).trans hsinB
  change 1/16 ≤ curvatureForAngle h a ∧ _ ∧ 1/64 ≤ curvatureForAngle h b ∧ _
  unfold curvatureForAngle
  refine ⟨?_,?_,?_,?_⟩
  · apply (le_div_iff₀ (sq_pos_of_pos hh)).mpr
    nlinarith only [(sq_le_sq₀ (by positivity : 0 ≤ h/8) hsA).mpr hsinA]
  · apply (div_lt_iff₀ (sq_pos_of_pos hh)).mpr
    nlinarith only [(sq_lt_sq₀ hsA (by positivity : 0 ≤ h/2)).mpr hupper]
  · apply (le_div_iff₀ (sq_pos_of_pos hh)).mpr
    nlinarith only [(sq_le_sq₀ (by positivity : 0 ≤ h/16) hsB).mpr hsinB]
  · apply div_lt_div_of_pos_right _ (sq_pos_of_pos hh)
    nlinarith only [(sq_lt_sq₀ hsB hsA).mpr hsm]

end BreakingResonance

#print axioms BreakingResonance.fastCurvature_bounds
