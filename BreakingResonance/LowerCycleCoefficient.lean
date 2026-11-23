import BreakingResonance.LowerCycleReturn
import BreakingResonance.LowerConeInvariant

noncomputable section

open Matrix
open scoped Matrix Matrix.Norms.Operator

namespace BreakingResonance

private theorem angle_halfLength_range {p : ℕ} (hp : 7 ≤ p) :
    0 < Real.pi/(2*(p:ℝ)) ∧ Real.pi/(2*(p:ℝ)) ≤ Real.pi/6 := by
  have hp₇ : 7 ≤ (p:ℝ) := by exact_mod_cast hp
  have hp₀ : 0 < (p:ℝ) := by linarith
  refine ⟨by positivity,?_⟩
  apply (div_le_iff₀ (by positivity : 0 < 2*(p:ℝ))).mpr
  have hm := mul_le_mul_of_nonneg_right hp₇ Real.pi_pos.le
  nlinarith only [hm,Real.pi_pos]

theorem cycleExpansionCoefficient_bounds {p : ℕ} (hp : 7 ≤ p) :
    let β := Real.pi/(2*(p:ℝ))
    4/5 ≤ Real.cos β ∧ Real.pi/(8*(p:ℝ)) ≤ cycleExpansionCoefficient p
      ∧ cycleExpansionCoefficient p < 1 := by
  let β := Real.pi/(2*(p:ℝ))
  obtain ⟨hβ,hβ₆⟩ := angle_halfLength_range hp
  change 0 < β at hβ
  change β ≤ Real.pi/6 at hβ₆
  have hπ := Real.pi_pos
  have hc : Real.cos (Real.pi/6) ≤ Real.cos β := Real.strictAntiOn_cos.antitoneOn
    ⟨hβ.le,by linarith only [hβ₆,hπ]⟩ ⟨by positivity,by linarith only [hπ]⟩ hβ₆
  have hcHalf : Real.cos (Real.pi/6) ≤ Real.cos (β/2) := Real.strictAntiOn_cos.antitoneOn
    ⟨by positivity,by linarith only [hβ₆,hπ]⟩ ⟨by positivity,by linarith only [hπ]⟩
    (by linarith only [hβ₆,hπ])
  have hsqrt : (8/5:ℝ) ≤ Real.sqrt 3 := by
    have h := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
    nlinarith only [h,Real.sqrt_nonneg 3,sq_nonneg (Real.sqrt 3-8/5)]
  rw [Real.cos_pi_div_six] at hc hcHalf
  have hc₀ : 0 < Real.cos β := by linarith only [hc,hsqrt]
  have hch₀ : 0 < Real.cos (β/2) := by linarith only [hcHalf,hsqrt]
  have htan := Real.le_tan (by positivity : 0 ≤ β/2) (by linarith only [hβ₆,hπ])
  have htanUpper : Real.tan (β/2) ≤ β := by
    rw [Real.tan_eq_sin_div_cos]
    apply (div_le_iff₀ hch₀).mpr
    have hs := Real.sin_le (show 0 ≤ β/2 by positivity)
    have hm := mul_le_mul_of_nonneg_right (show 1/2 ≤ Real.cos (β/2) by linarith) hβ.le
    nlinarith only [hm,hs]
  change 4/5 ≤ Real.cos β ∧ Real.pi/(8*(p:ℝ)) ≤ Real.tan (β/2)/(2*Real.cos β) ∧
    Real.tan (β/2)/(2*Real.cos β) < 1
  rw [show Real.pi/(8*(p:ℝ)) = β/4 by dsimp [β]; ring]
  refine ⟨by linarith,?_,?_⟩
  · apply (le_div_iff₀ (by positivity : 0 < 2*Real.cos β)).mpr
    have hm := mul_le_mul_of_nonneg_left (Real.cos_le_one β) hβ.le
    nlinarith only [hm,htan]
  · apply (div_lt_iff₀ (by positivity : 0 < 2*Real.cos β)).mpr
    linarith only [hβ₆,htanUpper,hc,hsqrt,Real.pi_lt_d2]

theorem cycleExpansionCoefficient_identity {p : ℕ} (hp : 7 ≤ p) :
    let α := Real.pi/(p:ℝ)
    let β := Real.pi/(2*(p:ℝ))
    orbitC α-(1/2:ℝ) • orbitC β =
      cycleExpansionCoefficient p • coneExpansionMatrix (Real.cos β) := by
  let β := Real.pi/(2*(p:ℝ))
  have hp₀ : 0 < (p:ℝ) := by exact_mod_cast (by omega : 0 < p)
  have he : Real.pi/(p:ℝ) = 2*β := by dsimp [β]; field_simp
  obtain ⟨hβ,hβ₆⟩ := angle_halfLength_range hp
  change 0 < β at hβ
  change β ≤ Real.pi/6 at hβ₆
  obtain ⟨hc,_,_⟩ := cycleExpansionCoefficient_bounds hp
  change 4/5 ≤ Real.cos β at hc
  have hc₀ : Real.cos β ≠ 0 := (show 0 < Real.cos β by linarith).ne'
  have hπ := Real.pi_pos
  have hs : Real.sin β ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi hβ (by linarith only [hβ₆,hπ])).ne'
  have hb : cycleExpansionCoefficient p = (1-Real.cos β)/(2*Real.sin β*Real.cos β) := by
    change Real.tan (β/2)/(2*Real.cos β) = _
    rw [Real.tan_eq_sin_div_cos, ← (cos_half_quotient hβ (by linarith only [hβ₆,hπ])).2]
    field_simp
  change orbitC (Real.pi/(p:ℝ))-(1/2:ℝ) • orbitC β = _
  rw [he,hb]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [orbitC,coneExpansionMatrix,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,
      Real.sin_two_mul,Real.cos_two_mul] <;> field_simp [hs,hc₀] <;> ring

/-- First-order remainder in (7.2), with the strict bound used at the two
boundaries of the return cone. -/
theorem cycleReturn_small_remainder {p : ℕ} (hp : 7 ≤ p) {δ : ℝ}
    (hδ : 0 < δ) (hδp : δ ≤ 1/(80*(p:ℝ)^2)) :
    let β := Real.pi/(2*(p:ℝ))
    ‖cycleReturnMatrix p δ-1-(δ*cycleExpansionCoefficient p) •
      coneExpansionMatrix (Real.cos β)‖ < δ*cycleExpansionCoefficient p/20 := by
  let β := Real.pi/(2*(p:ℝ))
  have hp₀ : 0 < (p:ℝ) := by exact_mod_cast (by omega : 0 < p)
  have h := cycleReturn_remainder hp hδ hδp
  change ‖cycleReturnMatrix p δ-1-δ • (orbitC (Real.pi/(p:ℝ))-(1/2:ℝ) • orbitC β)‖ ≤ _ at h
  rw [cycleExpansionCoefficient_identity hp,smul_smul] at h
  refine h.trans_lt ?_
  obtain ⟨_,hb,_⟩ := cycleExpansionCoefficient_bounds hp
  have h₁ := (le_div_iff₀ (show 0 < 80*(p:ℝ)^2 by positivity)).mp hδp
  have h₂ : 3/2*(p:ℝ)*δ < Real.pi/(160*(p:ℝ)) := by
    apply (lt_div_iff₀ (by positivity : 0 < 160*(p:ℝ))).mpr
    nlinarith only [h₁,Real.pi_gt_three]
  have h₃ : Real.pi/(160*(p:ℝ)) ≤ cycleExpansionCoefficient p/20 := by
    rw [show Real.pi/(160*(p:ℝ)) = (Real.pi/(8*(p:ℝ)))/20 by ring]
    exact div_le_div_of_nonneg_right hb (by norm_num)
  have h₄ := mul_lt_mul_of_pos_left (h₂.trans_le h₃) hδ
  nlinarith only [h₄]

end BreakingResonance

#print axioms BreakingResonance.cycleExpansionCoefficient_bounds
#print axioms BreakingResonance.cycleExpansionCoefficient_identity
#print axioms BreakingResonance.cycleReturn_small_remainder
