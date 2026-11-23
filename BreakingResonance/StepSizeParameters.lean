import BreakingResonance.MixingParameters

noncomputable section

namespace BreakingResonance

def upperStepConstant (δ η CT CR : ℝ) : ℝ :=
  max (16/Real.sqrt δ)
    (Real.sqrt (48/η)*max (Real.sqrt CR) (Real.sqrt CT*CR^(3/4:ℝ)))

theorem threeQuarterPow_sq {x : ℝ} (hx : 0 < x) :
    (x^(3/4:ℝ))^2 = x*Real.sqrt x := by
  rw [← Real.rpow_natCast,← Real.rpow_mul hx.le,Real.sqrt_eq_rpow]
  norm_num
  rw [show (3/2:ℝ) = 1+1/2 by norm_num,Real.rpow_add hx,Real.rpow_one]

/-- The step size conditions that follow from the explicit lower bound on N. -/
theorem mixing_step_parameters {m L LH δ η CT CR D R : ℝ}
    (hm : 0 < m) (hmL : m ≤ L) (hLH : 0 ≤ LH) (hδ : 0 < δ) (hδ₁ : δ ≤ 1)
    (hη : 0 < η) (hCT : 0 < CT) (hCR : 0 < CR) (hD : 1 ≤ D)
    (hR : 0 ≤ R) (hRD : R ≤ CR*D) (N : ℕ)
    (hN : upperStepConstant δ η CT CR *
      (Real.sqrt (L/m*D)+Real.sqrt LH*(D/m)^(3/4:ℝ)) ≤ (N:ℝ)) :
    let h := 4/((N:ℝ)*Real.sqrt m)
    (1 ≤ N) ∧ 16/Real.sqrt δ ≤ (N:ℝ) ∧ h^2*m ≤ δ/16 ∧
      h^2*(L*R+LH*(CT/Real.sqrt m)*R*Real.sqrt R) ≤ η/3 := by
  let h : ℝ := 4/((N:ℝ)*Real.sqrt m)
  let C := upperStepConstant δ η CT CR
  let r := Real.sqrt (48/η)
  let X := Real.sqrt (L/m*D)
  let Y := Real.sqrt LH*(D/m)^(3/4:ℝ)
  let A := Real.sqrt CR
  let B := Real.sqrt CT*CR^(3/4:ℝ)
  have hL := hm.trans_le hmL
  have hD₀ : 0 < D := by linarith
  have hs := Real.sqrt_pos.mpr hm
  have hδs := Real.sqrt_pos.mpr hδ
  have hC₀ : 0 < C := (div_pos (by norm_num) hδs).trans_le (le_max_left _ _)
  have hκD : 1 ≤ L/m*D := by
    have hκ := (one_le_div hm).mpr hmL
    nlinarith only [mul_le_mul hκ hD (by norm_num : (0:ℝ) ≤ 1) (by positivity : 0 ≤ L/m)]
  have hX : 1 ≤ X := by
    calc
      1 = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ X := Real.sqrt_le_sqrt hκD
  have hY : 0 ≤ Y := by dsimp [Y]; positivity
  have hsum : 1 ≤ X+Y := by linarith only [hX,hY]
  have hNc : C ≤ (N:ℝ) := by
    have h := mul_le_mul_of_nonneg_left hsum hC₀.le
    rw [mul_one] at h
    exact h.trans hN
  have hnδ : 16/Real.sqrt δ ≤ (N:ℝ) := (le_max_left _ _).trans hNc
  have hn₀ : 0 < (N:ℝ) := hC₀.trans_le hNc
  have hNp : 1 ≤ N := by exact_mod_cast (show 0 < N by exact_mod_cast hn₀)
  have htime : h^2*m = 16/(N:ℝ)^2 := by
    dsimp [h]
    rw [div_pow,mul_pow,Real.sq_sqrt hm.le]
    field_simp
    norm_num
  have hNδsq : 256 ≤ (N:ℝ)^2*δ := by
    have ha := (div_le_iff₀ hδs).mp hnδ
    have hsq := (sq_le_sq₀ (by norm_num : (0:ℝ)≤16) (by positivity)).mpr ha
    rw [mul_pow,Real.sq_sqrt hδ.le] at hsq
    norm_num at hsq ⊢
    exact hsq
  have hsmall : h^2*m ≤ δ/16 := by
    rw [htime,div_le_div_iff₀ (by positivity : 0 < (N:ℝ)^2) (by norm_num : (0:ℝ) < 16)]
    nlinarith only [hNδsq]
  refine ⟨hNp,hnδ,hsmall,?_⟩
  have hn : r*(A*X+B*Y) ≤ (N:ℝ) := by
    have hn' := mul_le_mul_of_nonneg_right (le_max_right (16/Real.sqrt δ) (r*max A B))
      (show 0 ≤ X+Y by linarith only [hsum])
    have hle : A*X+B*Y ≤ max A B*(X+Y) := by
      rw [mul_add]
      exact add_le_add (mul_le_mul_of_nonneg_right (le_max_left A B) (by linarith only [hX]))
        (mul_le_mul_of_nonneg_right (le_max_right A B) hY)
    have hh := mul_le_mul_of_nonneg_left hle (Real.sqrt_nonneg (48/η))
    change r*(A*X+B*Y) ≤ r*(max A B*(X+Y)) at hh
    rw [show r*(max A B*(X+Y)) = r*max A B*(X+Y) by ring] at hh
    exact hh.trans (hn'.trans hN)
  have hA : 0 ≤ A := Real.sqrt_nonneg _
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hX₀ := Real.sqrt_nonneg (L/m*D)
  have hR₁ : 0 ≤ CR*D := by positivity
  have hRpow : R*Real.sqrt R ≤ (CR*D)*Real.sqrt (CR*D) :=
    mul_le_mul hRD (Real.sqrt_le_sqrt hRD) (Real.sqrt_nonneg _) hR₁
  have hAsq : (A*X)^2 = CR*(L/m*D) := by
    dsimp [A,X]
    rw [mul_pow,Real.sq_sqrt hCR.le,Real.sq_sqrt (by positivity)]
  have hBsq : (B*Y)^2 =
      LH*(CT/Real.sqrt m)*((CR*D)*Real.sqrt (CR*D))/m := by
    dsimp [B,Y]
    rw [mul_pow,mul_pow,mul_pow,Real.sq_sqrt hCT.le,Real.sq_sqrt hLH,
      threeQuarterPow_sq hCR,threeQuarterPow_sq (div_pos hD₀ hm),
      Real.sqrt_mul hCR.le,Real.sqrt_div hD₀.le]
    ring
  have hterms : (L*R+LH*(CT/Real.sqrt m)*R*Real.sqrt R)/m ≤
      (A*X)^2+(B*Y)^2 := by
    rw [hAsq,hBsq]
    have hRpos := mul_le_mul_of_nonneg_left hRD hL.le
    have hRp := mul_le_mul_of_nonneg_left hRpow
      (show 0 ≤ LH*(CT/Real.sqrt m) by positivity)
    have he : L*R+LH*(CT/Real.sqrt m)*R*Real.sqrt R =
        L*R+LH*(CT/Real.sqrt m)*(R*Real.sqrt R) := by ring
    rw [he]
    refine (div_le_div_of_nonneg_right (add_le_add hRpos hRp) hm.le).trans_eq ?_
    ring
  have hsum_sq : (A*X)^2+(B*Y)^2 ≤ (A*X+B*Y)^2 := by
    nlinarith only [mul_nonneg (mul_nonneg hA hX₀) (mul_nonneg hB hY)]
  have hnL : 0 ≤ r*(A*X+B*Y) :=
    mul_nonneg (Real.sqrt_nonneg _) (add_nonneg (mul_nonneg hA hX₀) (mul_nonneg hB hY))
  have hsquare := (sq_le_sq₀ hnL hn₀.le).mpr hn
  rw [mul_pow, show r^2 = 48/η by exact Real.sq_sqrt (by positivity)] at hsquare
  have hm0 := (mul_le_mul_of_nonneg_left (hterms.trans hsum_sq)
    (show 0 ≤ 48/η by positivity)).trans hsquare
  have hm1 := (div_le_iff₀ hη).mp (show
      (48*((L*R+LH*(CT/Real.sqrt m)*R*Real.sqrt R)/m))/η ≤ (N:ℝ)^2 by
    simpa only [div_mul_eq_mul_div, mul_assoc] using hm0)
  let K := L*R+LH*(CT/Real.sqrt m)*R*Real.sqrt R
  have hm2 : 48*K ≤ (N:ℝ)^2*m*η := by
    have ht := mul_le_mul_of_nonneg_right hm1 hm.le
    change 48*(K/m)*m ≤ _ at ht
    rw [show 48*(K/m)*m = 48*K by field_simp] at ht
    nlinarith only [ht]
  change h^2*K ≤ η/3
  rw [show h^2 = 16/((N:ℝ)^2*m) by
    dsimp [h]; rw [div_pow,mul_pow,Real.sq_sqrt hm.le]; norm_num]
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (show 0 < (N:ℝ)^2*m by positivity)).mpr
  have he : (η/3)*((N:ℝ)^2*m) = ((N:ℝ)^2*m*η)/3 := by ring
  rw [he]
  linarith only [hm2]

end BreakingResonance

#print axioms BreakingResonance.mixing_step_parameters
