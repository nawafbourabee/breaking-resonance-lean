import BreakingResonance.GaussianWedge

noncomputable section

open MeasureTheory ProbabilityTheory Set PersistencePays
open scoped ENNReal

namespace BreakingResonance

theorem quadratic_positionGaussian {m : ℝ} (hm : 0 < m) :
    positionGibbs (fastPotential m m) = gaussianReal 0 ⟨m⁻¹,inv_nonneg.mpr hm.le⟩ := by
  let v : NNReal := ⟨m⁻¹,inv_nonneg.mpr hm.le⟩
  have hv : v ≠ 0 := by
    intro h
    have hv' : (v:ℝ) = 0 := by exact_mod_cast h
    exact (inv_ne_zero hm.ne') hv'
  have hf (x : ℝ) : Real.exp (-fastPotential m m x) = Real.exp (-(m/2)*x^2) := by
    unfold fastPotential
    split_ifs <;> congr 1 <;> ring
  change positionGibbs (fastPotential m m) = gaussianReal 0 v
  ext A hA
  rw [positionGibbs,tilted_apply_eq_ofReal_integral' _ hA,gaussianReal_apply_eq_integral 0 hv A]
  change ENNReal.ofReal (∫ x in A, Real.exp (-fastPotential m m x)/
    (∫ y, Real.exp (-fastPotential m m y))) = _
  simp_rw [hf]
  rw [integral_gaussian (m/2)]
  congr 1
  apply setIntegral_congr_fun hA
  intro x _
  rw [gaussianPDFReal]
  change Real.exp (-(m/2)*x^2)/Real.sqrt (Real.pi/(m/2)) =
    (Real.sqrt (2*Real.pi*m⁻¹))⁻¹ * Real.exp (-(x-0)^2/(2*m⁻¹))
  have h₁ : Real.pi/(m/2) = 2*Real.pi*m⁻¹ := by ring
  have h₂ : -(x-0)^2/(2*m⁻¹) = -(m/2)*x^2 := by field_simp; ring
  rw [h₁,h₂,div_eq_mul_inv,mul_comm]

/-- A narrower Gaussian in the first coordinate is bounded by 1/r times
the standard Gaussian density when its standard deviation is r ≤ 1. -/
theorem gaussianNarrower_le {r : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1) :
    gaussianReal 0 ⟨r^2,sq_nonneg _⟩ ≤ ENNReal.ofReal r⁻¹ • gaussianReal 0 1 := by
  let v : NNReal := ⟨r^2,sq_nonneg _⟩
  have hv : v ≠ 0 := by
    intro h
    have hv' : (v:ℝ) = 0 := by exact_mod_cast h
    exact (sq_pos_of_pos hr).ne' hv'
  change gaussianReal 0 v ≤ _
  rw [gaussianReal_of_var_ne_zero 0 hv,
    gaussianReal_of_var_ne_zero 0 (by norm_num : (1:NNReal) ≠ 0),
    ← withDensity_smul _ (measurable_gaussianPDF _ _)]
  apply withDensity_mono
  refine ae_of_all _ fun x => ?_
  change ENNReal.ofReal (gaussianPDFReal 0 v x) ≤
    ENNReal.ofReal r⁻¹*ENNReal.ofReal (gaussianPDFReal 0 1 x)
  rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hr.le)]
  apply ENNReal.ofReal_le_ofReal
  simp only [gaussianPDFReal,sub_zero,NNReal.coe_one,mul_one]
  change (Real.sqrt (2*Real.pi*r^2))⁻¹*Real.exp (-x^2/(2*r^2)) ≤
    r⁻¹*((Real.sqrt (2*Real.pi))⁻¹*Real.exp (-x^2/2))
  rw [Real.sqrt_mul (by positivity : 0 ≤ 2*Real.pi),Real.sqrt_sq hr.le,mul_inv,
    mul_comm (Real.sqrt (2*Real.pi))⁻¹ r⁻¹,mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hr.le)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  have hsq : r^2 ≤ 1 := by simpa using (sq_le_sq₀ hr.le zero_le_one).mpr hr₁
  have h := div_le_div_of_nonneg_left (sq_nonneg x) (by positivity : 0 < 2*r^2)
    (by linarith only [hsq] : 2*r^2 ≤ 2)
  simpa only [neg_div] using neg_le_neg h

theorem quadratic_phase_scale {m r : ℝ} (hm : 0 < m) :
    (phaseGibbs (fastPotential m m)).map (fun z : ℝ×ℝ => (r*Real.sqrt m*z.1,z.2)) =
      (gaussianReal 0 ⟨r^2,sq_nonneg _⟩).prod (gaussianReal 0 1) := by
  let v : NNReal := ⟨m⁻¹,inv_nonneg.mpr hm.le⟩
  rw [phaseGibbs,quadratic_positionGaussian hm,stdGaussian_real]
  change ((gaussianReal 0 v).prod (gaussianReal 0 1)).map
    (Prod.map (fun x => (r*Real.sqrt m)*x) id) = _
  rw [← Measure.map_prod_map _ _ (by fun_prop) measurable_id,
    gaussianReal_map_const_mul,Measure.map_id,mul_zero]
  congr 2
  apply NNReal.eq
  change (r*Real.sqrt m)^2*m⁻¹ = r^2
  rw [mul_pow,Real.sq_sqrt hm.le]
  field_simp

def scalarVerletCrossing (m h : ℝ) (j : ℕ) : Set (ℝ×ℝ) :=
  {z | z.1 ≤ 0 ∧ 0 < (trajectory (fastGradient m m) h z j).1}

set_option maxHeartbeats 800000 in
/-- The phase-space probability of a proposed crossing in the slow
coordinate, with the constant of Appendix B. -/
theorem scalarVerletCrossing_bound {m h : ℝ} (hm : 0 < m) (hh : 0 < h)
    (ha₁ : h*Real.sqrt m ≤ 1) (j : ℕ) :
    phaseGibbs (fastPotential m m) (scalarVerletCrossing m h j) ≤
      ENNReal.ofReal (2/(3*Real.pi)*(h*Real.sqrt m)*(j:ℝ)) := by
  let a := h*Real.sqrt m
  let r := Real.sqrt (1-a^2/4)
  let θ := 2*Real.arcsin (a/2)
  let t := (j:ℝ)*θ
  let F (z : ℝ×ℝ) : ℝ×ℝ := (r*Real.sqrt m*z.1,z.2)
  have hsm : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm
  have ha : 0 < a := by positivity
  obtain ⟨hr,hr₁,hr₂,hθ,hθ₂,_,_⟩ := gaussianVerlet_angle ha ha₁
  change 0 < r at hr
  change r ≤ 1 at hr₁
  change 3/4 ≤ r^2 at hr₂
  change 0 < θ at hθ
  change θ ≤ a/r at hθ₂
  have ht : 0 ≤ t := by positivity
  have hF : Measurable F := by unfold F; fun_prop
  have he : F ⁻¹' gaussianWedge t = scalarVerletCrossing m h j := by
    ext z
    have hz := gaussianVerlet_position hm hh ha₁ z j
    change Real.sqrt m*(trajectory (fastGradient m m) h z j).1 =
      Real.cos t*(Real.sqrt m*z.1)+Real.sin t/r*z.2 at hz
    have hprod : Real.cos t*(r*Real.sqrt m*z.1)+Real.sin t*z.2 =
        r*(Real.sqrt m*(trajectory (fastGradient m m) h z j).1) := by
      rw [hz]
      field_simp [hr.ne']
    change (r*Real.sqrt m*z.1 ≤ 0 ∧
      0 < Real.cos t*(r*Real.sqrt m*z.1)+Real.sin t*z.2) ↔
      (z.1 ≤ 0 ∧ 0 < (trajectory (fastGradient m m) h z j).1)
    rw [hprod,mul_pos_iff_of_pos_left hr,mul_pos_iff_of_pos_left hsm]
    constructor
    · exact fun ⟨h₁,h₂⟩ => ⟨nonpos_of_mul_nonpos_right h₁ (mul_pos hr hsm),h₂⟩
    · exact fun ⟨h₁,h₂⟩ => ⟨mul_nonpos_of_nonneg_of_nonpos (mul_pos hr hsm).le h₁,h₂⟩
  have hrcomp : (gaussianReal 0 ⟨r^2,sq_nonneg _⟩).prod (gaussianReal 0 1) ≤
      ENNReal.ofReal r⁻¹ • standardNormalPair := by
    rw [standardNormalPair,← Measure.prod_smul_left]
    exact Measure.prod_mono (gaussianNarrower_le hr hr₁) le_rfl
  rw [← he,← Measure.map_apply hF (gaussianWedge_measurable t),quadratic_phase_scale hm]
  apply le_trans (hrcomp _)
  rw [Measure.smul_apply,smul_eq_mul]
  apply le_trans (mul_le_mul_right (gaussianWedge_probability ht) _)
  rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hr.le)]
  apply ENNReal.ofReal_le_ofReal
  have hden : 0 < 2*Real.pi*r^2 := by positivity
  have hscale : r⁻¹*(t/(2*Real.pi)) ≤ (j:ℝ)*a/(2*Real.pi*r^2) := by
    have hmul := mul_le_mul_of_nonneg_left hθ₂ (show 0 ≤ (j:ℝ) by positivity)
    have ht' : t ≤ ((j:ℝ)*a)/r := by simpa only [mul_div_assoc] using hmul
    calc
      _ ≤ r⁻¹*((((j:ℝ)*a)/r)/(2*Real.pi)) :=
        mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right ht' (by positivity)) (inv_nonneg.mpr hr.le)
      _ = _ := by
        field_simp [hr.ne',Real.pi_ne_zero]
  refine hscale.trans ?_
  apply (div_le_iff₀ hden).mpr
  change (j:ℝ)*a ≤ 2/(3*Real.pi)*a*(j:ℝ)*(2*Real.pi*r^2)
  have htmp := mul_le_mul_of_nonneg_right hr₂ (show 0 ≤ (j:ℝ)*a by positivity)
  have he' : 2/(3*Real.pi)*a*(j:ℝ)*(2*Real.pi*r^2) = (4/3)*((j:ℝ)*a)*r^2 := by
    field_simp [Real.pi_ne_zero]
    ring
  rw [he']
  nlinarith only [htmp]

end BreakingResonance

#print axioms BreakingResonance.quadratic_positionGaussian
#print axioms BreakingResonance.gaussianNarrower_le
#print axioms BreakingResonance.scalarVerletCrossing_bound
