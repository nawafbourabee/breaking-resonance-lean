import BreakingResonance.LowerConstructedTarget
import BreakingResonance.LowerProductEnergyTail

noncomputable section

open MeasureTheory Set PersistencePays
open scoped ENNReal

namespace BreakingResonance

def lowerEnergyCutoff (κ : ℝ) : ℝ :=
  2*(Fintype.card (LowerCoordinate κ):ℝ)+12*Real.log κ

def lowerNoExpander (κ h δ : ℝ) :
    Set (EuclideanSpace ℝ (LowerCoordinate κ) × EuclideanSpace ℝ (LowerCoordinate κ)) :=
  (phaseCoordinates (LowerCoordinate κ)) ⁻¹'
    (univ.pi (fun i => match i with
      | .inl _ => (expandingSet h (cycleHalfLength h) δ)ᶜ
      | .inr _ => univ))

def lowerHighEnergy (κ h δ : ℝ) :
    Set (EuclideanSpace ℝ (LowerCoordinate κ) × EuclideanSpace ℝ (LowerCoordinate κ)) :=
  {z | lowerEnergyCutoff κ < phaseEnergy (lowerPotential κ h δ) z}

def lowerBadPhase (κ h δ : ℝ) :
    Set (EuclideanSpace ℝ (LowerCoordinate κ) × EuclideanSpace ℝ (LowerCoordinate κ)) :=
  lowerNoExpander κ h δ ∪ lowerHighEnergy κ h δ

theorem lowerPotential_measurable (κ h δ : ℝ) : Measurable (lowerPotential κ h δ) :=
  (continuous_iff_continuousAt.mpr (fun x =>
    (separablePotential_gradient (lowerCurvatureNeg κ h δ) (lowerCurvaturePos κ h δ) x).differentiableAt.continuousAt)).measurable

theorem lowerBadPhase_measurable (κ h δ : ℝ) : MeasurableSet (lowerBadPhase κ h δ) := by
  apply MeasurableSet.union
  · apply (phaseCoordinates (LowerCoordinate κ)).measurable
    apply MeasurableSet.univ_pi
    intro i
    cases i
    · exact (measurableSet_expandingSet h (cycleHalfLength h) δ).compl
    · exact MeasurableSet.univ
  · exact measurableSet_lt measurable_const
      (measurable_phaseEnergy _ (lowerPotential_measurable κ h δ))

theorem lowerNoExpander_bound {κ h δ : ℝ} (hκ : 64 ≤ κ) (hh : 0 < h) (hh₁ : h ≤ 1)
    (hδ : 0 < δ) (hδp : δ ≤ 1/(80*(cycleHalfLength h:ℝ)^2)) :
    (phaseGibbs (lowerPotential κ h δ)) (lowerNoExpander κ h δ) ≤ ENNReal.ofReal (κ⁻¹^6) := by
  let ι := LowerCoordinate κ
  let a := lowerCurvatureNeg κ h δ
  let b := lowerCurvaturePos κ h δ
  let U := lowerPotential κ h δ
  let q : ℝ := 1/1000
  let E := expandingSet h (cycleHalfLength h) δ
  let μ (i : ι) := phaseGibbs (fastPotential (a i) (b i))
  let C (i : ι) : Set (ℝ×ℝ) := match i with
    | .inl _ => Eᶜ
    | .inr _ => univ
  let e := phaseCoordinates ι
  have hκ₀ : 0 < κ := by linarith only [hκ]
  have hcurv := lowerCurvature_bounds hκ hh hh₁ hδ hδp
  have ha (i : ι) : 0 < a i := (inv_pos.mpr hκ₀).trans_le (hcurv i).1
  have hab (i : ι) : a i ≤ b i := (hcurv i).2.1
  have (i : ι) : IsProbabilityMeasure (μ i) := by
    have hI := fastPotential_gibbs_integrable (ha i) (hab i)
    have : IsProbabilityMeasure (positionGibbs (fastPotential (a i) (b i))) :=
      isProbabilityMeasure_tilted hI
    unfold μ phaseGibbs
    infer_instance
  have hC (i : ι) : MeasurableSet (C i) := by
    cases i
    · exact (measurableSet_expandingSet h (cycleHalfLength h) δ).compl
    · exact MeasurableSet.univ
  have hcoord : (phaseGibbs U).map e = Measure.pi μ :=
    separablePhaseGibbs_coordinates a b ha hab
  have hp (i : Fin (expandingCoordinateCount κ)) :
      μ (Sum.inl i) (C (Sum.inl i)) ≤ ENNReal.ofReal (1-q) := by
    have hP : ENNReal.ofReal q ≤ μ (.inl i) E :=
      expandingSet_gibbs_probability hh hh₁ hδ hδp
    change μ (.inl i) Eᶜ ≤ _
    rw [prob_compl_eq_one_sub (measurableSet_expandingSet h (cycleHalfLength h) δ),
      ENNReal.ofReal_sub 1 (by positivity : 0 ≤ q),ENNReal.ofReal_one]
    exact tsub_le_tsub_left hP 1
  change (phaseGibbs U) (e ⁻¹' univ.pi C) ≤ _
  rw [← e.map_apply (univ.pi C),hcoord,Measure.pi_pi,Fintype.prod_sum_type]
  have hPbest : (∏ i : Fin (expandingCoordinateCount κ), μ (.inl i) (C (.inl i))) ≤
      (ENNReal.ofReal (1-q))^expandingCoordinateCount κ := by
    calc
      _ ≤ ∏ _i : Fin (expandingCoordinateCount κ), ENNReal.ofReal (1-q) :=
        Finset.prod_le_prod' (fun i _ => hp i)
      _ = _ := by simp
  have haux : (∏ i : Fin 2, μ (.inr i) (C (.inr i))) = 1 := by
    simp [C]
  rw [haux,mul_one]
  apply hPbest.trans
  rw [← ENNReal.ofReal_pow (by norm_num [q] : 0 ≤ 1-q)]
  apply ENNReal.ofReal_le_ofReal
  have hstep : 1-q ≤ Real.exp (-q) := by
    linarith only [Real.add_one_le_exp (-q)]
  have hgrow := pow_le_pow_left₀ (by norm_num [q] : 0 ≤ 1-q) hstep (expandingCoordinateCount κ)
  rw [← Real.exp_nat_mul] at hgrow
  apply hgrow.trans
  have hn : 6*q⁻¹*Real.log κ ≤ (expandingCoordinateCount κ:ℝ) := Nat.le_ceil _
  have hcost : 6*Real.log κ ≤ (expandingCoordinateCount κ:ℝ)*q := by
    have hm := mul_le_mul_of_nonneg_right hn (show 0 ≤ q by positivity)
    norm_num [q] at hm ⊢
    linarith only [hm]
  have hk : κ⁻¹^6 = Real.exp ((6:ℕ)*(-Real.log κ)) := by
    rw [Real.exp_nat_mul,Real.exp_neg,Real.exp_log hκ₀]
  rw [hk]
  apply Real.exp_le_exp.mpr
  push_cast
  nlinarith only [hcost]

theorem lowerHighEnergy_bound {κ h δ : ℝ} (hκ : 64 ≤ κ) (hh : 0 < h) (hh₁ : h ≤ 1)
    (hδ : 0 < δ) (hδp : δ ≤ 1/(80*(cycleHalfLength h:ℝ)^2)) :
    (phaseGibbs (lowerPotential κ h δ)) (lowerHighEnergy κ h δ) ≤ ENNReal.ofReal (κ⁻¹^6) := by
  let a := lowerCurvatureNeg κ h δ
  let b := lowerCurvaturePos κ h δ
  let U := lowerPotential κ h δ
  let H := phaseEnergy U
  let μ := phaseGibbs U
  let d := Fintype.card (LowerCoordinate κ)
  let R := lowerEnergyCutoff κ
  have hκ₀ : 0 < κ := by linarith only [hκ]
  have hcurv := lowerCurvature_bounds hκ hh hh₁ hδ hδp
  have ha (i : LowerCoordinate κ) : 0 < a i := (inv_pos.mpr hκ₀).trans_le (hcurv i).1
  have hab (i : LowerCoordinate κ) : a i ≤ b i := (hcurv i).2.1
  obtain ⟨hI,hM⟩ := separable_phase_exp_moment a b ha hab
  change (∫ z, Real.exp (H z/2) ∂μ) = 2^d at hM
  have hmarkov := mul_meas_ge_le_integral_of_nonneg (ae_of_all _ (fun _ => Real.exp_nonneg _))
    hI (Real.exp (R/2))
  change Real.exp (R/2)*μ.real {z | Real.exp (R/2) ≤ Real.exp (H z/2)}
    ≤ ∫ z, Real.exp (H z/2) ∂μ at hmarkov
  rw [hM] at hmarkov
  have hm : Real.exp (R/2)*μ.real (lowerHighEnergy κ h δ) ≤ 2^d := by
    apply le_trans _ hmarkov
    apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
    apply measureReal_mono _ (by finiteness)
    intro z hz
    exact Real.exp_le_exp.mpr (by change R < H z at hz; linarith only [hz])
  have hnum : (2:ℝ)^d ≤ Real.exp (R/2)*(κ⁻¹^6) := by
    have hsmall : (2:ℝ)^d ≤ Real.exp (d:ℝ) := by
      have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) Real.exp_one_gt_two.le d
      simpa only [← Real.exp_nat_mul, mul_one] using h
    have he : Real.exp (R/2)*(κ⁻¹^6) = Real.exp (d:ℝ) := by
      have hk : κ⁻¹^6 = Real.exp (-6*Real.log κ) := by
        nth_rw 1 [← Real.exp_log hκ₀]
        rw [← Real.exp_neg, ← Real.exp_nat_mul]
        push_cast
        congr 1
        ring
      rw [hk,← Real.exp_add]
      congr 1
      unfold R lowerEnergyCutoff d
      ring
    rw [he]
    exact hsmall
  have hr : μ.real (lowerHighEnergy κ h δ) ≤ κ⁻¹^6 :=
    (le_of_mul_le_mul_left (hm.trans hnum) (Real.exp_pos _))
  rw [← ENNReal.ofReal_toReal (measure_ne_top μ (lowerHighEnergy κ h δ))]
  exact ENNReal.ofReal_le_ofReal hr

theorem lowerBadPhase_bound {κ h δ : ℝ} (hκ : 64 ≤ κ) (hh : 0 < h) (hh₁ : h ≤ 1)
    (hδ : 0 < δ) (hδp : δ ≤ 1/(80*(cycleHalfLength h:ℝ)^2)) :
    (phaseGibbs (lowerPotential κ h δ)) (lowerBadPhase κ h δ) ≤ ENNReal.ofReal (2*κ⁻¹^6) := by
  unfold lowerBadPhase
  refine (measure_union_le _ _).trans ?_
  refine (add_le_add (lowerNoExpander_bound hκ hh hh₁ hδ hδp)
    (lowerHighEnergy_bound hκ hh hh₁ hδ hδp)).trans ?_
  rw [← ENNReal.ofReal_add (by positivity : 0 ≤ κ⁻¹^6) (by positivity : 0 ≤ κ⁻¹^6)]
  apply ENNReal.ofReal_le_ofReal
  ring_nf
  exact le_rfl

end BreakingResonance

#print axioms BreakingResonance.lowerNoExpander_bound
#print axioms BreakingResonance.lowerHighEnergy_bound
#print axioms BreakingResonance.lowerBadPhase_bound
