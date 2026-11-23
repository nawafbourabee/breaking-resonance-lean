import BreakingResonance.LowerAngles

noncomputable section

open Set

namespace BreakingResonance

def returnCone (z : ℝ×ℝ) : Prop :=
  0 < z.1 ∧ -4*z.1 ≤ z.2 ∧ z.2 ≤ -3*z.1

theorem sin_ge_sin_of_between {u t : ℝ} (hu : 0 ≤ u) (hu₁ : u ≤ Real.pi/2)
    (ht : u ≤ t) (ht' : t ≤ Real.pi-u) : Real.sin u ≤ Real.sin t := by
  have huI : u ∈ Icc (-(Real.pi/2)) (Real.pi/2) :=
    ⟨by linarith only [hu,Real.pi_pos],hu₁⟩
  by_cases hs : t ≤ Real.pi/2
  · exact Real.strictMonoOn_sin.monotoneOn huI
      ⟨huI.1.trans ht,hs⟩ ht
  · rw [← Real.sin_pi_sub t]
    apply Real.strictMonoOn_sin.monotoneOn huI
    · constructor <;> linarith only [ht',hu,Real.pi_pos,le_of_not_ge hs]
    · linarith only [ht']

theorem iterate_agrees_on_prefix {X : Type*} (f g : X → X) (z : X) (n : ℕ)
    (h : ∀ j < n, f (g^[j] z) = g (g^[j] z)) :
    f^[n] z = g^[n] z := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply',Function.iterate_succ_apply',
      ih (fun j hj => h j (hj.trans n.lt_succ_self))]
    exact h n n.lt_succ_self

/-- Strict signs and the lower bound on intermediate positions over the
two harmonic blocks of one return cycle. -/
theorem lowerOrbit_signs {p : ℕ} (hp : 7 ≤ p) {δ : ℝ} (hδ : 0 < δ)
    (hδ₁ : δ ≤ 1/(80*(p:ℝ)^2)) {x y : ℝ} (hx : 0 < x) (hy : y ≤ -3*x) :
    let a := fastAnglePos p δ
    let b := fastAngleNeg p δ
    let z := (harmonicStep a)^[p] (x,y)
    (∀ j < p, x/2 ≤ ((harmonicStep a)^[j] (x,y)).1) ∧
      ∀ j < 2*p, ((harmonicStep b)^[j] z).1 ≤ -(x/2) := by
  let a := fastAnglePos p δ
  let b := fastAngleNeg p δ
  let z := (harmonicStep a)^[p] (x,y)
  have hpr : 7 ≤ (p:ℝ) := by exact_mod_cast hp
  have hpp : 0 < (p:ℝ) := by linarith only [hpr]
  have hpNat : 0 < p := by omega
  obtain ⟨hb,hb₁,hba,haπ,hab,hpa,hpb⟩ := fastAngle_bounds hp hδ hδ₁
  have ha : 0 < a := hb.trans hba
  have hsa : 0 < Real.sin a := Real.sin_pos_of_pos_of_lt_pi ha
    (by linarith only [haπ,Real.pi_pos])
  have hsb : 0 < Real.sin b := Real.sin_pos_of_pos_of_lt_pi hb
    (by linarith only [haπ,hba,Real.pi_pos])
  have hδsmall : δ ≤ 1/80 := hδ₁.trans (by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    nlinarith only [hpr,sq_nonneg ((p:ℝ)-7)])
  have ha_lower : Real.pi/(p:ℝ) ≤ a :=
    (div_le_iff₀ hpp).mpr (by linarith only [hpa,hδ])
  have haδ : δ ≤ a/2 := by
    have hq : δ ≤ 1/(p:ℝ) := hδ₁.trans
      (div_le_div_of_nonneg_left (by norm_num) hpp (by nlinarith only [hpr,sq_nonneg ((p:ℝ)-7)]))
    have hlow := div_le_div_of_nonneg_right (show (2:ℝ) ≤ Real.pi by
      linarith only [Real.pi_gt_three]) hpp.le
    rw [show 2/(p:ℝ) = 2*(1/(p:ℝ)) by ring] at hlow
    linarith only [hq,hlow,ha_lower]
  have hδsa : δ ≤ Real.sin a/4 := by
    have htrig := Real.mul_le_sin ha.le (by linarith only [haπ,Real.pi_pos])
    have hlow := mul_le_mul_of_nonneg_left ha_lower (show 0 ≤ 2/Real.pi by positivity)
    rw [show (2/Real.pi)*(Real.pi/(p:ℝ)) = 2/(p:ℝ) by field_simp] at hlow
    have hδbase : δ ≤ 1/(2*(p:ℝ)) := hδ₁.trans
      (div_le_div_of_nonneg_left (by norm_num) (by positivity)
        (by nlinarith only [hpr,sq_nonneg ((p:ℝ)-7)]))
    rw [show 1/(2*(p:ℝ)) = (2/(p:ℝ))/4 by ring] at hδbase
    linarith only [htrig,hlow,hδbase]
  have hapos (j : ℕ) (hj : j < p) : x/2 ≤ ((harmonicStep a)^[j] (x,y)).1 := by
    by_cases hj₀ : j = 0
    · subst j
      simp
      linarith only [hx]
    have hjr : 1 ≤ (j:ℝ) := by exact_mod_cast (show 1 ≤ j by omega)
    have hjb : (j:ℝ)+1 ≤ (p:ℝ) := by exact_mod_cast hj
    have hlow : a-δ ≤ (j:ℝ)*a := by
      have h := mul_le_mul_of_nonneg_right hjr ha.le
      linarith only [h,hδ]
    have hup : (j:ℝ)*a ≤ Real.pi-(a-δ) := by
      have h := mul_le_mul_of_nonneg_right hjb ha.le
      linarith only [h,hpa]
    have hsa₁ := sin_ge_sin_of_between
      (show 0 ≤ a-δ by linarith only [haδ,ha])
      (show a-δ ≤ Real.pi/2 by linarith only [haπ,hδ,Real.pi_pos]) hlow hup
    have hlip := (abs_le.mp (Real.abs_sin_sub_sin_le (a-δ) a)).1
    rw [show a-δ-a = -δ by ring,abs_neg,abs_of_nonneg hδ.le] at hlip
    have hjSin : Real.sin a-δ ≤ Real.sin ((j:ℝ)*a) := by linarith only [hsa₁,hlip]
    have hnext : -δ ≤ Real.sin (((j:ℝ)+1)*a) := by
      by_cases hs : ((j:ℝ)+1)*a ≤ Real.pi
      · exact (neg_nonpos.mpr hδ.le).trans
          (Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) hs)
      · have hf := (abs_le.mp (Real.abs_sin_sub_sin_le (((j:ℝ)+1)*a) Real.pi)).1
        rw [Real.sin_pi,sub_zero,abs_of_nonneg (sub_nonneg.mpr (le_of_not_ge hs))] at hf
        have h := mul_le_mul_of_nonneg_right hjb ha.le
        linarith only [hf,h,hpa]
    have hm₁ := mul_le_mul_of_nonneg_right hnext hx.le
    have hm₂ := mul_le_mul hjSin (show 3*x ≤ -y by linarith only [hy])
      (by positivity : 0 ≤ 3*x) (by linarith only [hδsa,hsa,hjSin])
    have hm₃ := mul_le_mul_of_nonneg_right hδsa hx.le
    rw [harmonic_iterate a hsa.ne',Prod.fst]
    apply (le_div_iff₀ hsa).mpr
    nlinarith only [hm₁,hm₂,hm₃,mul_nonneg hsa.le hx.le]
  have hz₂ : x/2 ≤ z.2 := by
    have hpos := hapos (p-1) (by omega : p-1 < p)
    have hp' : p-1+1 = p := Nat.sub_add_cancel (by omega)
    change x/2 ≤ ((harmonicStep a)^[p] (x,y)).2
    rw [← hp',Function.iterate_succ_apply']
    exact hpos
  have hz₁ : z.1 ≤ -(x/2) := by
    have hδa : a+δ ≤ Real.pi/2 := by
      linarith only [haπ,hδsmall,Real.pi_gt_three]
    have hlow := Real.strictMonoOn_sin.monotoneOn
      (show a ∈ Icc (-(Real.pi/2)) (Real.pi/2) from
        ⟨by linarith only [ha,Real.pi_pos],by linarith only [haπ,Real.pi_pos]⟩)
      (show a+δ ∈ Icc (-(Real.pi/2)) (Real.pi/2) from
        ⟨by linarith only [ha,hδ,Real.pi_pos],hδa⟩)
      (by linarith only [hδ])
    have hsδ : 0 ≤ Real.sin δ := Real.sin_nonneg_of_nonneg_of_le_pi hδ.le
      (by linarith only [hδsmall,Real.pi_gt_three])
    have hsin (t : ℝ) : Real.sin (Real.pi+t) = -Real.sin t := by
      simp [Real.sin_add]
    change ((harmonicStep a)^[p] (x,y)).1 ≤ -(x/2)
    rw [harmonic_iterate a hsa.ne',Prod.fst,
      show ((p:ℝ)+1)*a = Real.pi+(a+δ) by linarith only [hpa],
      hpa,hsin,hsin]
    apply (div_le_iff₀ hsa).mpr
    nlinarith only [mul_le_mul_of_nonneg_right hlow hx.le,
      mul_nonpos_of_nonneg_of_nonpos hsδ (by linarith only [hy,hx] : y ≤ 0),
      mul_nonneg hx.le hsa.le]
  refine ⟨hapos,?_⟩
  intro j hj
  by_cases hj₀ : j = 0
  · subst j
    exact hz₁
  have hjr : 1 ≤ (j:ℝ) := by exact_mod_cast (show 1 ≤ j by omega)
  have hjb : (j:ℝ)+1 ≤ 2*(p:ℝ) := by exact_mod_cast hj
  have hfirst : Real.sin b ≤ Real.sin ((j:ℝ)*b) := by
    apply sin_ge_sin_of_between hb.le (by linarith only [hba,haπ,Real.pi_pos])
    · simpa using mul_le_mul_of_nonneg_right hjr hb.le
    · have h := mul_le_mul_of_nonneg_right hjb hb.le
      linarith only [h,hpb,hδ]
  have hsecond : 0 ≤ Real.sin (((j:ℝ)+1)*b) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by
      have h := mul_le_mul_of_nonneg_right hjb hb.le
      linarith only [h,hpb,hδ])
  have hm₁ := mul_nonpos_of_nonneg_of_nonpos hsecond (by linarith only [hz₁,hx] : z.1 ≤ 0)
  have hm₂ := mul_le_mul hfirst hz₂ (by linarith only [hx] : 0 ≤ x/2)
    (hsb.le.trans hfirst)
  rw [show (harmonicStep b)^[j] z = (harmonicStep b)^[j] (z.1,z.2) by rw [Prod.eta],
    harmonic_iterate b hsb.ne',Prod.fst]
  apply (div_le_iff₀ hsb).mpr
  nlinarith only [hm₁,hm₂]

end BreakingResonance

#print axioms BreakingResonance.lowerOrbit_signs
