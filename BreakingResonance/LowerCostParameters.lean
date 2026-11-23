import BreakingResonance.LowerRejectionCutoff
import BreakingResonance.LowerCost

noncomputable section

namespace BreakingResonance

def lowerPerturbation (h : ℝ) : ℝ := 1/(80*(cycleHalfLength h:ℝ)^2)

def lowerLambda (κ : ℝ) : ℝ := Real.log (Real.exp 1+Real.log κ)

def lowerCostFirst : ℝ := 1/(10*(2*Real.pi+1))

def lowerCostSecond : ℝ := (Real.pi/81920)*lowerCostFirst

theorem lowerPerturbation_pos {h : ℝ} (hh : 0 < h) (hh₁ : h ≤ 1) :
    0 < lowerPerturbation h := by
  obtain ⟨hp,_,_⟩ := cycleHalfLength_bounds hh hh₁
  have hp' : (0:ℝ) < cycleHalfLength h := by exact_mod_cast (by omega : 0 < cycleHalfLength h)
  unfold lowerPerturbation
  positivity

theorem lowerLambda_pos {κ : ℝ} (hκ : 64 ≤ κ) : 0 < lowerLambda κ := by
  unfold lowerLambda
  apply Real.log_pos
  have hl := Real.log_nonneg (by linarith only [hκ] : 1 ≤ κ)
  linarith only [hl,Real.exp_one_gt_two]

theorem lowerExpansion_final {h : ℝ} (hh : 0 < h) (hh₁ : h ≤ 1) :
    let p := cycleHalfLength h
    3*Real.pi/(2560*(p:ℝ)^3) ≤ Real.log (cycleExpansion p (lowerPerturbation h)) := by
  let p := cycleHalfLength h
  let δ := lowerPerturbation h
  let t := 4/5*δ*cycleExpansionCoefficient p
  obtain ⟨hp,_,_⟩ := cycleHalfLength_bounds hh hh₁
  obtain ⟨_,hb,hb₁⟩ := cycleExpansionCoefficient_bounds hp
  have hδ := lowerPerturbation_pos hh hh₁
  have hp' : 7 ≤ (p:ℝ) := by exact_mod_cast hp
  have hp₀ : 0 < (p:ℝ) := by linarith
  have hb₀ : 0 ≤ cycleExpansionCoefficient p :=
    (by positivity : 0 ≤ Real.pi/(8*(p:ℝ))).trans hb
  have ht : 0 ≤ t := by positivity
  have hδ₁ : δ ≤ 1/80 := by
    unfold δ lowerPerturbation
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    nlinarith only [hp',sq_nonneg ((p:ℝ)-7)]
  have ht₁ : t ≤ 1/15 := by
    have h := mul_le_mul_of_nonneg_left hb₁.le hδ.le
    dsimp only [t]
    nlinarith only [h,hδ₁]
  have hLog := Real.le_log_one_add_of_nonneg ht
  have hs : (15/16)*t ≤ 2*t/(t+2) := by
    apply (le_div_iff₀ (by positivity : 0 < t+2)).mpr
    nlinarith only [mul_le_mul_of_nonneg_left ht₁ ht,ht]
  apply le_trans _ (hs.trans hLog)
  dsimp only [t,δ,lowerPerturbation]
  have hv := mul_le_mul_of_nonneg_left hb (show 0 ≤ 3/4*(1/(80*(p:ℝ)^2)) by positivity)
  change 3*Real.pi/(2560*(p:ℝ)^3) ≤ (15/16)*(4/5*(1/(80*(p:ℝ)^2))*cycleExpansionCoefficient p)
  convert hv using 1 <;> field_simp <;> ring

theorem lowerLogCutoff_le {κ : ℝ} (hκ : 64 ≤ κ) :
    lowerLogCutoff κ ≤ 8*lowerLambda κ := by
  let b := Real.exp 1+Real.log κ
  have hκ₀ : 0 < κ := by linarith only [hκ]
  have hlog₀ : 0 ≤ Real.log κ := Real.log_nonneg (by linarith only [hκ])
  have hlog₄ : 4 ≤ Real.log κ := by
    rw [← Real.log_exp 4]
    apply Real.log_le_log (Real.exp_pos 4)
    have he := pow_le_pow_left₀ (Real.exp_nonneg 1)
      (Real.exp_one_lt_d9.le.trans (by norm_num : (2.7182818286:ℝ) ≤ 11/4)) 4
    have he4 : Real.exp 4 ≤ (11/4:ℝ)^4 := by simpa [← Real.exp_nat_mul] using he
    exact he4.trans (by linarith only [hκ])
  have hb : 6 ≤ b := by dsimp [b]; linarith only [hlog₄,Real.exp_one_gt_two]
  have hb₀ : 0 < b := by linarith only [hb]
  have hj : (expandingCoordinateCount κ:ℝ) ≤ 6000*Real.log κ+1 := by
    have h := Nat.ceil_lt_add_one (show 0 ≤ 6*(1/1000:ℝ)⁻¹*Real.log κ by positivity)
    change (expandingCoordinateCount κ:ℝ) < _ at h
    norm_num at h
    linarith only [h]
  have hcut : 20*(lowerEnergyCutoff κ+6*Real.log κ) ≤ 260000*(1+Real.log κ) := by
    unfold lowerEnergyCutoff
    rw [lowerCoordinate_card]
    push_cast
    linarith only [hj,hlog₀]
  have h₇ : (260000:ℝ) ≤ b^7 := le_trans (by norm_num : (260000:ℝ) ≤ 6^7)
    (pow_le_pow_left₀ (by norm_num) hb _)
  have h₈ := mul_le_mul h₇ (show 1+Real.log κ ≤ b by dsimp [b]; linarith only [Real.exp_one_gt_two])
    (by positivity : 0 ≤ 1+Real.log κ) (by positivity : 0 ≤ b^7)
  have hh : 20*(lowerEnergyCutoff κ+6*Real.log κ) ≤ b^8 := hcut.trans (by
    simpa only [pow_succ b 7] using h₈)
  unfold lowerLogCutoff lowerLambda
  change Real.log _ ≤ 8*Real.log b
  have hpos : 0 < 20*(lowerEnergyCutoff κ+6*Real.log κ) := by
    unfold lowerEnergyCutoff
    rw [lowerCoordinate_card]
    push_cast
    linarith only [hlog₄,Nat.cast_nonneg (α := ℝ) (expandingCoordinateCount κ)]
  have h := Real.log_le_log hpos hh
  simpa only [Real.log_pow,Nat.cast_ofNat] using h

end BreakingResonance

#print axioms BreakingResonance.lowerExpansion_final
#print axioms BreakingResonance.lowerLogCutoff_le
