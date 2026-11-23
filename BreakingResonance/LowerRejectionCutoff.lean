import BreakingResonance.LowerExceptionalEvents

noncomputable section

open MeasureTheory Set PersistencePays
open scoped ENNReal

namespace BreakingResonance

def lowerLogCutoff (κ : ℝ) : ℝ :=
  Real.log (20*(lowerEnergyCutoff κ+6*Real.log κ))

def lowerRejectionCount (κ h δ : ℝ) : ℕ :=
  let p := cycleHalfLength h
  cycleLength p * Nat.ceil (lowerLogCutoff κ/(2*Real.log (cycleExpansion p δ)))

theorem lowerLogCutoff_ge_one {κ : ℝ} (hκ : 64 ≤ κ) : 1 ≤ lowerLogCutoff κ := by
  have hlog : 0 ≤ Real.log κ := Real.log_nonneg (by linarith only [hκ])
  have hd : 2 ≤ (Fintype.card (LowerCoordinate κ):ℝ) := by
    rw [lowerCoordinate_card]
    exact_mod_cast (show 2 ≤ expandingCoordinateCount κ+2 by omega)
  have hv : Real.exp 1 ≤ 20*(lowerEnergyCutoff κ+6*Real.log κ) := by
    unfold lowerEnergyCutoff
    linarith only [hd,hlog,Real.exp_one_lt_three]
  unfold lowerLogCutoff
  rw [← Real.log_exp 1]
  exact Real.log_le_log (Real.exp_pos 1) hv

theorem lowerLogExpansion_bounds {p : ℕ} (hp : 7 ≤ p) {δ : ℝ}
    (hδ : 0 < δ) (hδp : δ ≤ 1/(80*(p:ℝ)^2)) :
    0 < Real.log (cycleExpansion p δ) ∧ Real.log (cycleExpansion p δ) ≤ 1/32 := by
  have hχ := cycleExpansion_gt_one hp hδ
  have hχ₀ : 0 < cycleExpansion p δ := zero_lt_one.trans hχ
  obtain ⟨_,_,hcoeff⟩ := cycleExpansionCoefficient_bounds hp
  have hp' : 7 ≤ (p:ℝ) := by exact_mod_cast hp
  have hd : δ ≤ 1/80 := hδp.trans (by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    nlinarith only [hp',sq_nonneg ((p:ℝ)-7)])
  refine ⟨Real.log_pos hχ,(Real.log_le_sub_one_of_pos hχ₀).trans ?_⟩
  have ht := mul_le_mul_of_nonneg_left hcoeff.le hδ.le
  unfold cycleExpansion
  nlinarith only [ht,hd]

theorem lowerRejectionCount_horizon {κ h δ : ℝ} (hκ : 64 ≤ κ) (hh : 0 < h) (hh₁ : h ≤ 1)
    (hδ : 0 < δ) (hδp : δ ≤ 1/(80*(cycleHalfLength h:ℝ)^2)) :
    (lowerRejectionCount κ h δ:ℝ)*h+2 ≤
      12*lowerLogCutoff κ/Real.log (cycleExpansion (cycleHalfLength h) δ) := by
  let p := cycleHalfLength h
  let χ := cycleExpansion p δ
  let u := lowerLogCutoff κ
  let v := Real.log χ
  obtain ⟨hp,_,hph⟩ := cycleHalfLength_bounds hh hh₁
  obtain ⟨hv,hv₁⟩ := lowerLogExpansion_bounds hp hδ hδp
  have hu : 1 ≤ u := lowerLogCutoff_ge_one hκ
  have hj : (Nat.ceil (u/(2*v)):ℝ) ≤ u/(2*v)+1 :=
    (Nat.ceil_lt_add_one (show 0 ≤ u/(2*v) by positivity)).le
  have hp22 : (cycleLength p:ℝ)*h ≤ 22 := by
    unfold cycleLength
    push_cast
    linarith only [hph,Real.pi_lt_d2]
  have hterm := mul_le_mul hp22 hj (Nat.cast_nonneg _) (by norm_num : (0:ℝ) ≤ 22)
  have hvpos : 0 < v := hv
  have huv : 0 ≤ u/v := by positivity
  have h24 : 24 ≤ u/v := (le_div_iff₀ hvpos).mpr (by linarith only [hu,hv₁])
  change ((cycleLength p * Nat.ceil (u/(2*v)):ℕ):ℝ)*h+2 ≤ 12*u/v
  push_cast
  have he : u/(2*v) = (u/v)/2 := by ring
  conv_rhs at hterm => rw [he]
  rw [mul_div_assoc]
  nlinarith only [hterm,h24]

theorem lowerBadPhase_compl_properties {κ h δ : ℝ}
    {z : EuclideanSpace ℝ (LowerCoordinate κ) × EuclideanSpace ℝ (LowerCoordinate κ)}
    (hz : z ∉ lowerBadPhase κ h δ) :
    (∃ i : Fin (expandingCoordinateCount κ), (z.1 (Sum.inl i),z.2 (Sum.inl i)) ∈
      expandingSet h (cycleHalfLength h) δ) ∧
      phaseEnergy (lowerPotential κ h δ) z ≤ lowerEnergyCutoff κ := by
  simp only [lowerBadPhase,Set.mem_union,not_or] at hz
  refine ⟨?_,le_of_not_gt hz.2⟩
  by_contra! hn
  apply hz.1
  change phaseCoordinates (LowerCoordinate κ) z ∈ univ.pi _
  rw [mem_univ_pi]
  intro i
  rcases i with i | i
  · exact hn i
  · exact mem_univ _

set_option maxHeartbeats 800000 in
/-- The total energy increase in (7.12) follows from a single expanding
coordinate, with all coordinate energies nonnegative. -/
theorem lowerEnergyIncrease {κ h δ : ℝ} (hκ : 64 ≤ κ) (hh : 0 < h) (hh₁ : h ≤ 1)
    (hδ : 0 < δ) (hδp : δ ≤ 1/(80*(cycleHalfLength h:ℝ)^2))
    {z : EuclideanSpace ℝ (LowerCoordinate κ) × EuclideanSpace ℝ (LowerCoordinate κ)}
    (hz : z ∉ lowerBadPhase κ h δ) {J : ℕ} (hJ : lowerRejectionCount κ h δ ≤ J) :
    6*Real.log κ ≤
      phaseEnergy (lowerPotential κ h δ) (trajectory (lowerForce κ h δ) h z J)
        -phaseEnergy (lowerPotential κ h δ) z := by
  classical
  let p := cycleHalfLength h
  let χ := cycleExpansion p δ
  let u := lowerLogCutoff κ
  let v := Real.log χ
  let k := Nat.ceil (u/(2*v))
  let w := trajectory (lowerForce κ h δ) h z J
  let a := lowerCurvatureNeg κ h δ
  let b := lowerCurvaturePos κ h δ
  obtain ⟨hp,_,_⟩ := cycleHalfLength_bounds hh hh₁
  obtain ⟨hv,_⟩ := lowerLogExpansion_bounds hp hδ hδp
  have hχ : 0 < χ := zero_lt_one.trans (cycleExpansion_gt_one hp hδ)
  have hvpos : 0 < v := hv
  have hcard : 0 < cycleLength p := by unfold cycleLength; omega
  obtain ⟨⟨i,hi⟩,hR⟩ := lowerBadPhase_compl_properties hz
  have hG : lowerEnergyCutoff κ+6*Real.log κ ≤ χ^(2*(J/cycleLength p))/20 := by
    have hk : k ≤ J/cycleLength p := (Nat.le_div_iff_mul_le hcard).mpr (by
      rw [Nat.mul_comm]
      exact hJ)
    have hk' : (k:ℝ) ≤ (J/cycleLength p:ℕ) := by exact_mod_cast hk
    have hku := (div_le_iff₀ (show 0 < 2*v by positivity)).mp (Nat.le_ceil (u/(2*v)))
    have hl := mul_le_mul_of_nonneg_right hk' (show 0 ≤ 2*v by positivity)
    have hu : u ≤ (2*(J/cycleLength p):ℕ)*v := by push_cast; nlinarith only [hku,hl]
    have he := Real.exp_le_exp.mpr hu
    rw [Real.exp_nat_mul,Real.exp_log hχ] at he
    have harg : 0 < 20*(lowerEnergyCutoff κ+6*Real.log κ) := by
      unfold lowerEnergyCutoff
      have hlog := Real.log_nonneg (by linarith only [hκ] : 1 ≤ κ)
      have hd : 2 ≤ (Fintype.card (LowerCoordinate κ):ℝ) := by
        rw [lowerCoordinate_card]
        exact_mod_cast (show 2 ≤ expandingCoordinateCount κ+2 by omega)
      linarith only [hlog,hd]
    change Real.exp (Real.log (20*(lowerEnergyCutoff κ+6*Real.log κ))) ≤ _ at he
    rw [Real.exp_log harg] at he
    linarith only [he]
  have hmode := hG.trans (expandingSet_energy_lower hh hh₁ hδ hδp hi J)
  have hproj := lowerPhase_fast_projection κ h δ z J i
  change (w.1 (Sum.inl i),w.2 (Sum.inl i)) = _ at hproj
  rw [← hproj] at hmode
  have htotal :
      fastEnergy h p δ (w.1 (Sum.inl i),w.2 (Sum.inl i)) ≤
        phaseEnergy (lowerPotential κ h δ) w := by
    change phaseEnergy (fastPotential (a (Sum.inl i)) (b (Sum.inl i))) _ ≤
      phaseEnergy (separablePotential a b) w
    rw [separableEnergy]
    apply Finset.single_le_sum (f := fun j => phaseEnergy (fastPotential (a j) (b j)) (w.1 j,w.2 j))
    · intro j _
      rw [phaseEnergy_eq_norm]
      have hcurv := lowerCurvature_bounds hκ hh hh₁ hδ hδp j
      have ha : 0 ≤ a j := (show 0 ≤ κ⁻¹ by positivity).trans hcurv.1
      have hb : 0 ≤ b j := ha.trans hcurv.2.1
      unfold fastPotential
      split_ifs <;> positivity
    · exact Finset.mem_univ _
  have he := hmode.trans htotal
  linarith only [he,hR]

end BreakingResonance

#print axioms BreakingResonance.lowerRejectionCount_horizon
#print axioms BreakingResonance.lowerEnergyIncrease
