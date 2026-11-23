import BreakingResonance.LowerAcceptance

noncomputable section

open MeasureTheory ProbabilityTheory Set PersistencePays
open scoped ENNReal ProbabilityTheory

namespace BreakingResonance

def lowerSlowHalfspace (κ : ℝ) : Set (EuclideanSpace ℝ (LowerCoordinate κ)) :=
  {x | 0 ≤ x (Sum.inr (1:Fin 2))}

theorem lowerSlowHalfspace_measurable (κ : ℝ) :
    MeasurableSet (lowerSlowHalfspace κ) := by
  exact measurableSet_le measurable_const ((PiLp.proj (𝕜 := ℝ) (p := 2)
    (β := fun _ : LowerCoordinate κ => ℝ) (Sum.inr (1:Fin 2))).continuous.measurable)

theorem scalarQuadratic_halfspace {c : ℝ} (hc : 0 < c) :
    positionGibbs (fastPotential c c) (Ici 0) = 1/2 := by
  rw [positionGibbs,tilted_apply_eq_ofReal_integral' _ measurableSet_Ici]
  have hf (x : ℝ) : Real.exp (-(fastPotential c c x)) = Real.exp (-(c/2)*x^2) := by
    unfold fastPotential
    split_ifs <;> congr 1 <;> ring
  change ENNReal.ofReal (∫ x in Ici (0:ℝ),
    Real.exp (-fastPotential c c x)/(∫ y, Real.exp (-fastPotential c c y))) = _
  simp_rw [hf]
  rw [integral_div,integral_gaussian,integral_Ici_eq_integral_Ioi,integral_gaussian_Ioi]
  have h : 0 < Real.sqrt (Real.pi/(c/2)) := by positivity
  rw [show (Real.sqrt (Real.pi/(c/2))/2)/(Real.sqrt (Real.pi/(c/2))) = 1/2 by field_simp]
  rw [ENNReal.ofReal_div_of_pos (by norm_num : 0 < (2:ℝ)),ENNReal.ofReal_one]
  norm_num

theorem lowerSlowHalfspace_mass {κ h δ : ℝ} (hκ : 64 ≤ κ) (hh : 0 < h) (hh₁ : h ≤ 1)
    (hδ : 0 < δ) (hδp : δ ≤ 1/(80*(cycleHalfLength h:ℝ)^2)) :
    positionGibbs (lowerPotential κ h δ) (lowerSlowHalfspace κ) = 1/2 := by
  let a := lowerCurvatureNeg κ h δ
  let b := lowerCurvaturePos κ h δ
  let U := lowerPotential κ h δ
  let μ := phaseGibbs U
  let ι := LowerCoordinate κ
  let i : ι := Sum.inr (1:Fin 2)
  let μi (j : ι) := phaseGibbs (fastPotential (a j) (b j))
  let e := phaseCoordinates ι
  have hκ₀ : 0 < κ := by linarith only [hκ]
  have hcurv := lowerCurvature_bounds hκ hh hh₁ hδ hδp
  have ha (j : ι) : 0 < a j := (inv_pos.mpr hκ₀).trans_le (hcurv j).1
  have hab (j : ι) : a j ≤ b j := (hcurv j).2.1
  have (j : ι) : IsProbabilityMeasure (μi j) := by
    have : IsProbabilityMeasure (positionGibbs (fastPotential (a j) (b j))) :=
      isProbabilityMeasure_tilted (fastPotential_gibbs_integrable (ha j) (hab j))
    unfold μi phaseGibbs
    infer_instance
  have he : MeasurePreserving e μ (Measure.pi μi) :=
    ⟨e.measurable,separablePhaseGibbs_coordinates a b ha hab⟩
  have heval := (measurePreserving_eval (μ := μi) i).comp he
  let C : Set (ℝ×ℝ) := Ici 0 ×ˢ univ
  have hC : MeasurableSet C := measurableSet_Ici.prod MeasurableSet.univ
  have hm : μ (((Function.eval i) ∘ e) ⁻¹' C) = μi i C := by
    calc
      _ = (μ.map ((Function.eval i) ∘ e)) C := (Measure.map_apply heval.measurable hC).symm
      _ = _ := by rw [heval.map_eq]
  have hE : ((Function.eval i) ∘ e) ⁻¹' C = (lowerSlowHalfspace κ) ×ˢ univ := by
    ext z
    simp [phaseCoordinates_apply,Function.eval,lowerSlowHalfspace,C,e,i]
  rw [hE] at hm
  have hcc : a i = κ⁻¹ ∧ b i = κ⁻¹ := by norm_num [a,b,i,lowerCurvatureNeg,lowerCurvaturePos,lowerAuxCurvature]
  change phaseGibbs U (lowerSlowHalfspace κ ×ˢ univ) = (phaseGibbs (fastPotential (a i) (b i))) C at hm
  rw [hcc.1,hcc.2,phaseGibbs,phaseGibbs,Measure.prod_prod,Measure.prod_prod,
    measure_univ,mul_one,measure_univ,mul_one,scalarQuadratic_halfspace (inv_pos.mpr hκ₀)] at hm
  exact hm

def lowerWarmStart (κ h δ : ℝ) : Measure (EuclideanSpace ℝ (LowerCoordinate κ)) :=
  (2:ℝ≥0∞) • (positionGibbs (lowerPotential κ h δ)).restrict (lowerSlowHalfspace κ)

theorem lowerWarmStart_probability {κ h δ : ℝ} (hκ : 64 ≤ κ) (hh : 0 < h) (hh₁ : h ≤ 1)
    (hδ : 0 < δ) (hδp : δ ≤ 1/(80*(cycleHalfLength h:ℝ)^2)) :
    IsProbabilityMeasure (lowerWarmStart κ h δ) := by
  refine ⟨?_⟩
  rw [lowerWarmStart,Measure.smul_apply,Measure.restrict_apply_univ,
    lowerSlowHalfspace_mass hκ hh hh₁ hδ hδp,smul_eq_mul,one_div,
    ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]

theorem lowerWarmStart_good_mass {κ h δ : ℝ} (hκ : 64 ≤ κ) (hh : 0 < h) (hh₁ : h ≤ 1)
    (hδ : 0 < δ) (hδp : δ ≤ 1/(80*(cycleHalfLength h:ℝ)^2)) :
    1-4*κ⁻¹^4 ≤ (lowerWarmStart κ h δ).real
      (lowerSlowHalfspace κ ∩ lowerGoodPositions κ h δ) := by
  let π := positionGibbs (lowerPotential κ h δ)
  let A := lowerSlowHalfspace κ
  let G := lowerGoodPositions κ h δ
  have hA : MeasurableSet A := lowerSlowHalfspace_measurable κ
  have hG : MeasurableSet G := lowerGoodPositions_measurable κ h δ
  have hκ₀ : 0 < κ := by linarith only [hκ]
  have hAreal : π.real A = 1/2 := by
    rw [Measure.real,show π A = 1/2 from lowerSlowHalfspace_mass hκ hh hh₁ hδ hδp]
    norm_num
  have hC := lowerGoodPositions_compl_bound hκ hh hh₁ hδ hδp
  have hGreal : π.real Gᶜ ≤ 2*κ⁻¹^4 := by
    have h := ENNReal.toReal_mono (by finiteness) hC
    rw [ENNReal.toReal_ofReal (by positivity)] at h
    exact h
  have hs : A ⊆ (A ∩ G) ∪ Gᶜ := by
    intro x hx
    by_cases hg : x ∈ G
    · exact Or.inl ⟨hx,hg⟩
    · exact Or.inr hg
  have hsub := measureReal_mono (μ := π) hs (by finiteness)
  have hb := hsub.trans (measureReal_union_le (μ := π) (A ∩ G) Gᶜ)
  have he : A ∩ G ∩ A = A ∩ G := by ext x; simp only [mem_inter_iff]; tauto
  change 1-4*κ⁻¹^4 ≤ (lowerWarmStart κ h δ).real (A∩G)
  rw [lowerWarmStart,Measure.real,Measure.smul_apply,Measure.restrict_apply (hA.inter hG),
    he,smul_eq_mul,ENNReal.toReal_mul]
  change _ ≤ (2:ℝ≥0∞).toReal*π.real (A∩G)
  norm_num
  rw [inv_pow] at hGreal
  linarith only [hAreal,hGreal,hb]

end BreakingResonance

#print axioms BreakingResonance.lowerSlowHalfspace_mass
#print axioms BreakingResonance.lowerWarmStart_probability
#print axioms BreakingResonance.lowerWarmStart_good_mass
