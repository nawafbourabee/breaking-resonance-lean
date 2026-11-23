import BreakingResonance.LowerProductGibbs

noncomputable section

open MeasureTheory PersistencePays Set

namespace BreakingResonance

def expandingCoordinateCount (κ : ℝ) : ℕ :=
  Nat.ceil (6*(1/1000:ℝ)⁻¹*Real.log κ)

abbrev LowerCoordinate (κ : ℝ) := Fin (expandingCoordinateCount κ) ⊕ Fin 2

def lowerAuxCurvature (κ : ℝ) (i : Fin 2) : ℝ := if i = 0 then 1 else κ⁻¹

def lowerCurvatureNeg (κ h δ : ℝ) : LowerCoordinate κ → ℝ
  | .inl _ => curvatureForAngle h (fastAngleNeg (cycleHalfLength h) δ)
  | .inr i => lowerAuxCurvature κ i

def lowerCurvaturePos (κ h δ : ℝ) : LowerCoordinate κ → ℝ
  | .inl _ => curvatureForAngle h (fastAnglePos (cycleHalfLength h) δ)
  | .inr i => lowerAuxCurvature κ i

def lowerPotential (κ h δ : ℝ) : EuclideanSpace ℝ (LowerCoordinate κ) → ℝ :=
  separablePotential (lowerCurvatureNeg κ h δ) (lowerCurvaturePos κ h δ)

def lowerForce (κ h δ : ℝ) : EuclideanSpace ℝ (LowerCoordinate κ) → EuclideanSpace ℝ (LowerCoordinate κ) :=
  separableForce (lowerCurvatureNeg κ h δ) (lowerCurvaturePos κ h δ)

theorem lowerCoordinate_card (κ : ℝ) :
    Fintype.card (LowerCoordinate κ) = expandingCoordinateCount κ+2 := by
  simp

theorem lowerCurvature_bounds {κ h δ : ℝ} (hκ : 64 ≤ κ) (hh : 0 < h) (hh₁ : h ≤ 1)
    (hδ : 0 < δ) (hδp : δ ≤ 1/(80*(cycleHalfLength h:ℝ)^2)) (i : LowerCoordinate κ) :
    κ⁻¹ ≤ lowerCurvatureNeg κ h δ i ∧
      lowerCurvatureNeg κ h δ i ≤ lowerCurvaturePos κ h δ i ∧ lowerCurvaturePos κ h δ i ≤ 1 := by
  have hκ₀ : 0 < κ := by linarith only [hκ]
  have hinv : κ⁻¹ ≤ 1/64 := by
    rw [← one_div κ]
    exact one_div_le_one_div_of_le (by norm_num) hκ
  obtain ⟨_,hA,hb,hba⟩ := fastCurvature_bounds hh hh₁ hδ hδp
  rcases i with i | i
  · exact ⟨hinv.trans hb,hba.le,hA.le⟩
  · change κ⁻¹ ≤ lowerAuxCurvature κ i ∧ _ ∧ lowerAuxCurvature κ i ≤ 1
    unfold lowerAuxCurvature
    split_ifs <;> exact ⟨by linarith only [hinv],le_rfl,by linarith only [hinv]⟩

theorem lowerPotential_gibbs_integrable {κ h δ : ℝ} (hκ : 64 ≤ κ) (hh : 0 < h) (hh₁ : h ≤ 1)
    (hδ : 0 < δ) (hδp : δ ≤ 1/(80*(cycleHalfLength h:ℝ)^2)) :
    Integrable (fun x => Real.exp (-lowerPotential κ h δ x)) volume := by
  have hcurv := lowerCurvature_bounds hκ hh hh₁ hδ hδp
  have hκ₀ : 0 < κ := by linarith only [hκ]
  exact separablePotential_gibbs_integrable _ _
    (fun i => (inv_pos.mpr hκ₀).trans_le (hcurv i).1) (fun i => (hcurv i).2.1)

theorem lowerPotential_conditions {κ h δ : ℝ} (hκ : 64 ≤ κ) (hh : 0 < h) (hh₁ : h ≤ 1)
    (hδ : 0 < δ) (hδp : δ ≤ 1/(80*(cycleHalfLength h:ℝ)^2)) :
    StrongConvexOn univ κ⁻¹ (lowerPotential κ h δ) ∧
      LipschitzWith 1 (lowerForce κ h δ) ∧
      ∀ x, HasGradientAt (lowerPotential κ h δ) (lowerForce κ h δ x) x := by
  have hcurv := lowerCurvature_bounds hκ hh hh₁ hδ hδp
  have hκ₀ : 0 < κ := by linarith only [hκ]
  refine ⟨separablePotential_strongConvex _ _ _ (fun i => (hcurv i).1) (fun i => (hcurv i).2.1),?_,?_⟩
  · apply separableForce_lipschitz _ _ (fun i => (hcurv i).2.1)
      (fun i => (inv_pos.mpr hκ₀).le.trans (hcurv i).1)
    simpa using fun i => (hcurv i).2.2
  · exact separablePotential_gradient _ _

theorem lowerPhase_fast_projection (κ h δ : ℝ)
    (z : EuclideanSpace ℝ (LowerCoordinate κ) × EuclideanSpace ℝ (LowerCoordinate κ)) (n : ℕ)
    (i : Fin (expandingCoordinateCount κ)) :
    ((trajectory (lowerForce κ h δ) h z n).1 (Sum.inl i),
      (trajectory (lowerForce κ h δ) h z n).2 (Sum.inl i)) =
    fastOrbit h (cycleHalfLength h) δ (z.1 (Sum.inl i),z.2 (Sum.inl i)) n :=
  separableTrajectory _ _ h z n (Sum.inl i)

end BreakingResonance

#print axioms BreakingResonance.lowerPotential_conditions
#print axioms BreakingResonance.lowerPhase_fast_projection
