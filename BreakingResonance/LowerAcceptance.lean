import BreakingResonance.LowerRejectionCutoff
import BreakingResonance.RoundingCost

noncomputable section

open MeasureTheory ProbabilityTheory Set PersistencePays
open scoped ENNReal ProbabilityTheory

namespace BreakingResonance

def lowerBadVelocityProbability (κ h δ : ℝ) (x : EuclideanSpace ℝ (LowerCoordinate κ)) : ℝ≥0∞ :=
  stdGaussian (EuclideanSpace ℝ (LowerCoordinate κ)) (Prod.mk x ⁻¹' lowerBadPhase κ h δ)

def lowerGoodPositions (κ h δ : ℝ) : Set (EuclideanSpace ℝ (LowerCoordinate κ)) :=
  {x | lowerBadVelocityProbability κ h δ x ≤ ENNReal.ofReal (κ⁻¹^2)}

theorem lowerBadVelocityProbability_measurable (κ h δ : ℝ) :
    Measurable (lowerBadVelocityProbability κ h δ) :=
  measurable_measure_prodMk_left (lowerBadPhase_measurable κ h δ)

theorem lowerGoodPositions_measurable (κ h δ : ℝ) :
    MeasurableSet (lowerGoodPositions κ h δ) :=
  measurableSet_le (lowerBadVelocityProbability_measurable κ h δ) measurable_const

theorem lowerGoodPositions_compl_bound {κ h δ : ℝ} (hκ : 64 ≤ κ) (hh : 0 < h) (hh₁ : h ≤ 1)
    (hδ : 0 < δ) (hδp : δ ≤ 1/(80*(cycleHalfLength h:ℝ)^2)) :
    positionGibbs (lowerPotential κ h δ) (lowerGoodPositions κ h δ)ᶜ ≤
      ENNReal.ofReal (2*κ⁻¹^4) := by
  let π := positionGibbs (lowerPotential κ h δ)
  let f := lowerBadVelocityProbability κ h δ
  let e := ENNReal.ofReal (κ⁻¹^2)
  have hκ₀ : 0 < κ := by linarith only [hκ]
  have hmf := mul_meas_ge_le_lintegral (μ := π) (lowerBadVelocityProbability_measurable κ h δ) e
  have hJ : (∫⁻ x, f x ∂π) ≤ ENNReal.ofReal (2*κ⁻¹^6) := by
    have hb := lowerBadPhase_bound hκ hh hh₁ hδ hδp
    unfold phaseGibbs at hb
    rw [Measure.prod_apply (lowerBadPhase_measurable κ h δ)] at hb
    exact hb
  have hm : e*π (lowerGoodPositions κ h δ)ᶜ ≤ ENNReal.ofReal (2*κ⁻¹^6) := by
    refine le_trans ?_ (hmf.trans hJ)
    apply mul_le_mul_right
    apply measure_mono
    intro x hx
    change ¬ f x ≤ e at hx
    exact (lt_of_not_ge hx).le
  have hex : ENNReal.ofReal (2*κ⁻¹^6) = e*ENNReal.ofReal (2*κ⁻¹^4) := by
    rw [← ENNReal.ofReal_mul (show 0 ≤ κ⁻¹^2 by positivity)]
    congr 1
    ring
  rw [hex] at hm
  exact (ENNReal.mul_le_mul_iff_right (by unfold e; positivity) (by unfold e; simp)).mp hm

/-- Rounding down and adding a Bernoulli draw can enter the short-count
event only if the sampled duration is less than the corresponding horizon. -/
theorem roundedDuration_short_bound {h : ℝ} (hh : 0 < h) (ρ : Measure ℝ) (j : ℕ) :
    roundedDurationLaw h ρ (Iio j) ≤ ρ (Iio ((j:ℝ)*h)) := by
  have hj : MeasurableSet (Iio j) := measurableSet_Iio
  rw [roundedDurationLaw,Measure.add_apply,Measure.smul_apply,Measure.smul_apply,
    Measure.map_apply (measurable_floorDuration h) hj,
    Measure.map_apply (measurable_succFloorDuration h) hj,smul_eq_mul,smul_eq_mul]
  have h₁ : (fun τ : ℝ => Nat.floor (τ/h)) ⁻¹' Iio j ⊆ Iio ((j:ℝ)*h) := by
    intro τ hτ
    have hjlt : Nat.floor (τ/h) < j := hτ
    have hm : ((Nat.floor (τ/h)+1:ℕ):ℝ) ≤ (j:ℝ) := by exact_mod_cast hjlt
    have ht := (Nat.lt_floor_add_one (τ/h)).trans_le (by simpa using hm)
    exact (div_lt_iff₀ hh).mp ht
  have h₂ : (fun τ : ℝ => Nat.floor (τ/h)+1) ⁻¹' Iio j ⊆
      (fun τ : ℝ => Nat.floor (τ/h)) ⁻¹' Iio j :=
    fun τ hτ => Nat.lt_of_succ_lt (show Nat.floor (τ/h)+1 < j from hτ)
  calc
    _ ≤ (1/2:ℝ≥0∞)*ρ (Iio ((j:ℝ)*h))+(1/2:ℝ≥0∞)*ρ (Iio ((j:ℝ)*h)) :=
      add_le_add (mul_le_mul_right (measure_mono h₁) _) (mul_le_mul_right (measure_mono (h₂.trans h₁)) _)
    _ = _ := by
      have hh : (1/2:ℝ≥0∞)+(1/2)=1 := by
        rw [← two_mul,one_div,ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]
      rw [← add_mul,hh,one_mul]

def lowerAcceptanceBound (κ h δ : ℝ) : ℝ :=
  min 1 (12*lowerLogCutoff κ/(Real.sqrt κ*Real.log (cycleExpansion (cycleHalfLength h) δ)))

set_option maxHeartbeats 800000 in
theorem lowerEstimate_acceptance {κ h δ T : ℝ} (hκ : 64 ≤ κ) (hh : 0 < h) (hh₁ : h ≤ 1)
    (hδ : 0 < δ) (hδp : δ ≤ 1/(80*(cycleHalfLength h:ℝ)^2))
    (hT : 2*Real.sqrt κ ≤ T) (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    (hρ : ∀ t : ℝ, 0 ≤ t → ρ (Iio t) ≤ ENNReal.ofReal (2*t/T))
    {x : EuclideanSpace ℝ (LowerCoordinate κ)} (hx : x ∈ lowerGoodPositions κ h δ) :
    (∫⁻ z, acceptProbability (verletLogAcceptance (lowerPotential κ h δ) (lowerForce κ h δ) h) (x,z)
      ∂((roundedDurationLaw h ρ).prod (stdGaussian (EuclideanSpace ℝ (LowerCoordinate κ))))) ≤
      ENNReal.ofReal (lowerAcceptanceBound κ h δ) := by
  let E := EuclideanSpace ℝ (LowerCoordinate κ)
  let Jlaw := roundedDurationLaw h ρ
  let G := stdGaussian E
  let μ := Jlaw.prod G
  let j₀ := lowerRejectionCount κ h δ
  let t₀ := (j₀:ℝ)*h
  let C : Set (ℕ×E) := Iio j₀ ×ˢ univ
  let B : Set (ℕ×E) := univ ×ˢ (Prod.mk x ⁻¹' lowerBadPhase κ h δ)
  let f (z : ℕ×E) :=
    acceptProbability (verletLogAcceptance (lowerPotential κ h δ) (lowerForce κ h δ) h) (x,z)
  have hκ₀ : 0 < κ := by linarith only [hκ]
  have hκ₁ : 1 ≤ κ := by linarith only [hκ]
  have hsq : 0 < Real.sqrt κ := Real.sqrt_pos.mpr hκ₀
  have hT₀ : 0 < T := (by positivity : 0 < 2*Real.sqrt κ).trans_le hT
  have ht₀ : 0 ≤ t₀ := by positivity
  have hbad : MeasurableSet (Prod.mk x ⁻¹' lowerBadPhase κ h δ) :=
    (lowerBadPhase_measurable κ h δ).preimage measurable_prodMk_left
  have hC : MeasurableSet C := measurableSet_Iio.prod MeasurableSet.univ
  have hB : MeasurableSet B := MeasurableSet.univ.prod hbad
  have hf (z : ℕ×E) : f z ≤ C.indicator (fun _ => 1) z+B.indicator (fun _ => 1) z+
      ENNReal.ofReal (κ⁻¹^6) := by
    by_cases hCz : z ∈ C
    · refine (acceptProbability_le_one _ _).trans ?_
      rw [indicator_of_mem hCz]
      exact (le_self_add : (1:ℝ≥0∞) ≤ 1+B.indicator (fun _ => 1) z).trans le_self_add
    by_cases hBz : z ∈ B
    · refine (acceptProbability_le_one _ _).trans ?_
      rw [indicator_of_notMem hCz,indicator_of_mem hBz,zero_add]
      exact le_self_add
    have hJ : j₀ ≤ z.1 := le_of_not_gt (fun hz => hCz ⟨hz,mem_univ _⟩)
    have hz : (x,z.2) ∉ lowerBadPhase κ h δ := fun hz => hBz ⟨mem_univ _,hz⟩
    have henergy := lowerEnergyIncrease hκ hh hh₁ hδ hδp hz hJ
    rw [indicator_of_notMem hCz,indicator_of_notMem hBz,zero_add,zero_add]
    unfold f acceptProbability verletLogAcceptance
    apply ENNReal.ofReal_le_ofReal
    apply (min_le_right _ _).trans
    have hk : κ⁻¹^6 = Real.exp ((6:ℕ)*(-Real.log κ)) := by
      rw [Real.exp_nat_mul,Real.exp_neg,Real.exp_log hκ₀]
    rw [hk]
    apply Real.exp_le_exp.mpr
    push_cast
    linarith only [henergy]
  have hsum : (∫⁻ z, f z ∂μ) ≤ Jlaw (Iio j₀)+
      lowerBadVelocityProbability κ h δ x+ENNReal.ofReal (κ⁻¹^6) := by
    apply le_trans (lintegral_mono hf)
    have hsumM : Measurable (fun z : ℕ×E =>
        C.indicator (fun _ => (1:ℝ≥0∞)) z+B.indicator (fun _ => 1) z) :=
      (measurable_const.indicator hC).add (measurable_const.indicator hB)
    rw [lintegral_add_left hsumM,lintegral_add_left (measurable_const.indicator hC),
      lintegral_indicator_const hC,
      lintegral_indicator_const hB,lintegral_const]
    simp [μ,C,B,Measure.prod_prod,lowerBadVelocityProbability,G]
    exact le_rfl
  have hj := (roundedDuration_short_bound hh ρ j₀).trans (hρ t₀ ht₀)
  have hquarter : 2*t₀/T ≤ t₀/Real.sqrt κ := by
    rw [div_le_div_iff₀ hT₀ hsq]
    nlinarith only [mul_le_mul_of_nonneg_left hT ht₀]
  have hsum' := hsum.trans (add_le_add_left
    (add_le_add (hj.trans (ENNReal.ofReal_le_ofReal hquarter)) hx) _)
  have hone : (∫⁻ z, f z ∂μ) ≤ 1 := (lintegral_mono (fun _ => acceptProbability_le_one _ _)).trans
    (by simp [μ])
  change (∫⁻ z, f z ∂μ) ≤ ENNReal.ofReal (lowerAcceptanceBound κ h δ)
  rw [lowerAcceptanceBound,ENNReal.ofReal_min,ENNReal.ofReal_one]
  apply le_min hone
  refine hsum'.trans ?_
  have hκpow (n : ℕ) (hn : 0 < n) : κ⁻¹^n ≤ (Real.sqrt κ)⁻¹ := by
    have hk : Real.sqrt κ ≤ κ := (sq_le_sq₀ hsq.le hκ₀.le).mp
      ((Real.sq_sqrt hκ₀.le).le.trans (by nlinarith only [sq_nonneg (κ-1),hκ₁]))
    have hs : κ⁻¹ ≤ (Real.sqrt κ)⁻¹ := inv_le_inv₀ hκ₀ hsq |>.mpr hk
    have hi : κ⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hκ₁
    have hb : κ⁻¹^n ≤ κ⁻¹^1 := pow_le_pow_of_le_one (by positivity) hi hn
    exact (hb.trans_eq (pow_one _)).trans hs
  rw [← ENNReal.ofReal_add (by positivity : 0 ≤ t₀/Real.sqrt κ) (by positivity : 0 ≤ κ⁻¹^2),
    ← ENNReal.ofReal_add (by positivity : 0 ≤ t₀/Real.sqrt κ+κ⁻¹^2) (by positivity : 0 ≤ κ⁻¹^6)]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ (t₀+2)/Real.sqrt κ := by
      rw [add_div,show (2:ℝ)/Real.sqrt κ = 2*(Real.sqrt κ)⁻¹ by ring]
      linarith only [hκpow 2 (by decide),hκpow 6 (by decide)]
    _ ≤ 12*lowerLogCutoff κ/(Real.log (cycleExpansion (cycleHalfLength h) δ))/Real.sqrt κ :=
      div_le_div_of_nonneg_right (lowerRejectionCount_horizon hκ hh hh₁ hδ hδp) hsq.le
    _ = _ := by ring

end BreakingResonance

#print axioms BreakingResonance.lowerGoodPositions_compl_bound
#print axioms BreakingResonance.roundedDuration_short_bound
#print axioms BreakingResonance.lowerEstimate_acceptance
