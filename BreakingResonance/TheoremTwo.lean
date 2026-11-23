import BreakingResonance.IndependentCounts
import BreakingResonance.LowerWarmStart
import BreakingResonance.LowerCostParameters
import BreakingResonance.LowerOptimalCurvature

noncomputable section

open MeasureTheory ProbabilityTheory Set PersistencePays
open scoped ENNReal

namespace BreakingResonance

/-- Expected new gradient evaluations in n complete Verlet proposals.
The fixed-count integrator uses one new gradient at each integration stage.
The law of the sequence of counts is the product of the rounded duration laws. -/
def expectedProposalGradients (h : ℝ) (ρ : Measure ℝ) (n : ℕ) : ℝ :=
  ∫ J : Fin n → ℕ, ∑ i, (J i:ℝ) ∂Measure.pi (fun _ => roundedDurationLaw h ρ)

theorem expectedProposalGradients_eq {h : ℝ} (hh : 0 < h) (ρ : Measure ℝ)
    [IsProbabilityMeasure ρ] (hτ : Integrable (fun τ : ℝ => τ) ρ)
    (hpos : ∀ᵐ τ ∂ρ, 0 ≤ τ) (n : ℕ) :
    expectedProposalGradients h ρ n = (n:ℝ)*(∫ j : ℕ, (j:ℝ) ∂roundedDurationLaw h ρ) := by
  exact (independentCountSum (roundedDurationLaw h ρ)
    (roundedDuration_integrable_mean h hh ρ hτ hpos).1 n).2

theorem lowerIteration_count {κ h δ T : ℝ} (hκ : 64 ≤ κ) (hh : 0 < h) (hh₁ : h ≤ 1)
    (hδ : 0 < δ) (hδp : δ ≤ 1/(80*(cycleHalfLength h:ℝ)^2))
    (hT : 2*Real.sqrt κ ≤ T) (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    (hρ : ∀ t : ℝ, 0 ≤ t → ρ (Iio t) ≤ ENNReal.ofReal (2*t/T))
    (n : ℕ)
    (htv : totalVariation
      (evolve (fun _ => roundedVerletKernel (lowerPotential κ h δ) (lowerPotential_measurable κ h δ)
        (lowerForce κ h δ) ((lowerPotential_conditions hκ hh hh₁ hδ hδp).2.1.continuous.measurable)
          h ρ) (lowerWarmStart κ h δ) n)
      (positionGibbs (lowerPotential κ h δ)) ≤ 1/4) :
    1/5 ≤ (n:ℝ) ∧
      Real.sqrt κ*Real.log (cycleExpansion (cycleHalfLength h) δ)/(60*lowerLogCutoff κ) ≤ (n:ℝ) := by
  let U := lowerPotential κ h δ
  let g := lowerForce κ h δ
  let hg := ((lowerPotential_conditions hκ hh hh₁ hδ hδp).2.1.continuous.measurable)
  let K := roundedVerletKernel U (lowerPotential_measurable κ h δ) g hg h ρ
  let π := positionGibbs U
  let ν := lowerWarmStart κ h δ
  let A := lowerSlowHalfspace κ
  let E := A ∩ lowerGoodPositions κ h δ
  let a := lowerAcceptanceBound κ h δ
  have : IsProbabilityMeasure π := isProbabilityMeasure_tilted (lowerPotential_gibbs_integrable hκ hh hh₁ hδ hδp)
  have : IsProbabilityMeasure ν := lowerWarmStart_probability hκ hh hh₁ hδ hδp
  have : IsMarkovKernel K := roundedVerletKernel_markov _ _ _ _ _ _
  have hκ₀ : 0 < κ := by linarith only [hκ]
  obtain ⟨hp,_,_⟩ := cycleHalfLength_bounds hh hh₁
  have hℓ : 0 < lowerLogCutoff κ := (by norm_num : (0:ℝ) < 1).trans_le (lowerLogCutoff_ge_one hκ)
  have hv := (lowerLogExpansion_bounds hp hδ hδp).1
  have ha : 0 < a := by
    unfold a lowerAcceptanceBound
    exact lt_min (by norm_num) (by positivity)
  have ha₁ : a ≤ 1 := min_le_left _ _
  have hA := lowerSlowHalfspace_measurable κ
  have hE := hA.inter (lowerGoodPositions_measurable κ h δ)
  have hπ : π.real A = 1/2 := by
    rw [Measure.real,show π A = 1/2 from lowerSlowHalfspace_mass hκ hh hh₁ hδ hδp]
    norm_num
  have hb : 4*κ⁻¹^4 ≤ 1/20 := by
    rw [inv_pow,← div_eq_mul_inv]
    exact initial_bad_mass_margin κ hκ
  have hkeep (x : EuclideanSpace ℝ (LowerCoordinate κ)) (hx : x ∈ E) :
      ENNReal.ofReal (1-a) ≤ K x E := by
    unfold K roundedVerletKernel randomizedVerletKernel
    apply proposalKernel_retains _ _ _ _ _ x E hE hx _ ha.le
    exact lowerEstimate_acceptance hκ hh hh₁ hδ hδp hT ρ hρ hx.2
  have hTV : totalVariation (evolve (fun _ => K) ν n) π ≤ 1/4 := htv
  have hn := attempts_lower_from_rejection K ν π A E hA hE inter_subset_left hπ a _
    ha ha₁ hb (lowerWarmStart_good_mass hκ hh hh₁ hδ hδp) hkeep n hTV
  refine ⟨?_,?_⟩
  · exact (one_div_le_one_div_of_le (by positivity : 0 < 5*a) (by linarith only [ha₁])).trans hn
  · apply le_trans _ hn
    have ha' : a ≤ 12*lowerLogCutoff κ/
        (Real.sqrt κ*Real.log (cycleExpansion (cycleHalfLength h) δ)) := min_le_right _ _
    have hm := (le_div_iff₀ (show 0 < Real.sqrt κ*Real.log (cycleExpansion (cycleHalfLength h) δ) by positivity)).mp ha'
    apply (le_div_iff₀ (show 0 < 5*a by positivity)).mpr
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (show 0 < 60*lowerLogCutoff κ by positivity)).mpr
    nlinarith only [hm]

set_option maxHeartbeats 800000 in
/-- Theorem 2 for the explicit target constructed in Section 7. The lower
bound uses the expectation of the gradient evaluations in the proposals.
Any additional evaluations, including initialization, only increase it. -/
theorem theoremTwo (κ h T : ℝ) (hκ : 64 ≤ κ) (hh : 0 < h) (hh₁ : h ≤ 1)
    (hT : 2*Real.sqrt κ ≤ T) (_hT₁ : T ≤ 4*Real.sqrt κ) :
    let δ := lowerPerturbation h
    let U := lowerPotential κ h δ
    let g := lowerForce κ h δ
    let π := positionGibbs U
    let ν := lowerWarmStart κ h δ
    let A := lowerSlowHalfspace κ
    let hg := ((lowerPotential_conditions hκ hh hh₁ (lowerPerturbation_pos hh hh₁) le_rfl).2.1.continuous.measurable)
    StrongConvexOn univ κ⁻¹ U ∧ LipschitzWith 1 g ∧ (∀ x, HasGradientAt U (g x) x) ∧
      (∀ m, StrongConvexOn univ m U → m ≤ κ⁻¹) ∧
      (∀ L : NNReal, LipschitzWith L g → 1 ≤ (L:ℝ)) ∧
      MeasurableSet A ∧ π A = 1/2 ∧ IsProbabilityMeasure ν ∧
      ∀ (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
       (_hρ : ∀ t : ℝ, 0 ≤ t → ρ (Iio t) ≤ ENNReal.ofReal (2*t/T))
       (_hpositive : ∀ᵐ τ ∂ρ, 0 < τ)
       (_hfinite : Integrable (fun τ : ℝ => τ) ρ)
       (_hmean : T/3 ≤ ∫ τ, τ ∂ρ)
       (n : ℕ),
       totalVariation (evolve (fun _ => roundedVerletKernel U (lowerPotential_measurable κ h δ)
         g hg h ρ) ν n) π ≤ 1/4 →
       lowerCostFirst^(2/3:ℝ)*lowerCostSecond^(1/3:ℝ)*κ^(2/3:ℝ)/
         (lowerLambda κ)^(1/3:ℝ) ≤ expectedProposalGradients h ρ n := by
  let δ := lowerPerturbation h
  let p := cycleHalfLength h
  have hδ := lowerPerturbation_pos hh hh₁
  have hδp : δ ≤ 1/(80*(p:ℝ)^2) := le_rfl
  obtain ⟨hStrong,hLipschitz,hGradient⟩ := lowerPotential_conditions hκ hh hh₁ hδ hδp
  refine ⟨hStrong,hLipschitz,hGradient,lowerPotential_optimal_strongConvex κ h δ,
    lowerForce_optimal_lipschitz κ h δ,lowerSlowHalfspace_measurable κ,
    lowerSlowHalfspace_mass hκ hh hh₁ hδ hδp,lowerWarmStart_probability hκ hh hh₁ hδ hδp,?_⟩
  intro ρ _ hρ hpos hfinite hmean n htv
  have hκ₀ : 0 < κ := by linarith only [hκ]
  have hΛ := lowerLambda_pos hκ
  have hnonneg : ∀ᵐ τ ∂ρ, 0 ≤ τ := hpos.mono fun _ h => h.le
  have hμ : 2*Real.sqrt κ/3 ≤ ∫ τ, τ ∂ρ := by linarith only [hT,hmean]
  have hcost := roundedDuration_mean_lower κ h hκ hh hh₁ ρ hfinite hnonneg hμ
  have hcostEq := expectedProposalGradients_eq hh ρ hfinite hnonneg n
  obtain ⟨hn₁,hn₂⟩ := lowerIteration_count hκ hh hh₁ hδ hδp hT ρ hρ n htv
  obtain ⟨hp,_,hph⟩ := cycleHalfLength_bounds hh hh₁
  have hp₀ : 0 < (p:ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hℓ : 0 < lowerLogCutoff κ := (by norm_num : (0:ℝ) < 1).trans_le (lowerLogCutoff_ge_one hκ)
  have hlogχ := (lowerLogExpansion_bounds hp hδ hδp).1
  have hc₁ : 0 < lowerCostFirst := by unfold lowerCostFirst; positivity
  have hc₂ : 0 < lowerCostSecond := by unfold lowerCostSecond; positivity
  have hunit : (p:ℝ)*Real.sqrt κ/(2*(2*Real.pi+1)) ≤
      ∫ j : ℕ, (j:ℝ) ∂roundedDurationLaw h ρ := by
    apply le_trans _ hcost
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hm := mul_le_mul_of_nonneg_right hph.le (show 0 ≤ 2*Real.sqrt κ by positivity)
    nlinarith only [hm]
  have hpay1 : lowerCostFirst*(p:ℝ)*Real.sqrt κ ≤ expectedProposalGradients h ρ n := by
    rw [hcostEq]
    have hm := mul_le_mul hn₁ hunit (by positivity : 0 ≤ (p:ℝ)*Real.sqrt κ/(2*(2*Real.pi+1)))
      (by positivity : 0 ≤ (n:ℝ))
    have he : lowerCostFirst*(p:ℝ)*Real.sqrt κ =
        (1/5)*((p:ℝ)*Real.sqrt κ/(2*(2*Real.pi+1))) := by
      unfold lowerCostFirst
      field_simp
      ring
    rw [he]
    exact hm
  have hpay2 : (p:ℝ)*κ*Real.log (cycleExpansion p δ)/(120*(2*Real.pi+1)*lowerLogCutoff κ) ≤
      expectedProposalGradients h ρ n := by
    rw [hcostEq]
    have hm := mul_le_mul hn₂ hunit (by positivity : 0 ≤ (p:ℝ)*Real.sqrt κ/(2*(2*Real.pi+1)))
      (by positivity : 0 ≤ (n:ℝ))
    let c := Real.log (cycleExpansion p δ)
    let u := lowerLogCutoff κ
    change (Real.sqrt κ*c/(60*u))*((p:ℝ)*Real.sqrt κ/(2*(2*Real.pi+1))) ≤ _ at hm
    have he : (p:ℝ)*κ*c/(120*(2*Real.pi+1)*u) =
        (Real.sqrt κ*c/(60*u))*((p:ℝ)*Real.sqrt κ/(2*(2*Real.pi+1))) := by
      calc
        _ = (p:ℝ)*(Real.sqrt κ)^2*c/(120*(2*Real.pi+1)*u) := by rw [Real.sq_sqrt hκ₀.le]
        _ = _ := by
          have hu : 0 < u := hℓ
          field_simp
          ring
    change (p:ℝ)*κ*c/(120*(2*Real.pi+1)*u) ≤ _
    rw [he]
    exact hm
  refine weighted_cost_lower _ _ _ _ _ _ hc₁ hc₂ hp₀ hκ₀ hΛ hpay1 (le_trans ?_ hpay2)
  have hm := lowerExpansion_final hh hh₁
  have hcut := lowerLogCutoff_le hκ
  have hs : (Real.pi/81920)*lowerCostFirst*κ/((p:ℝ)^2*lowerLambda κ) =
      (p:ℝ)*κ*(3*Real.pi/(2560*(p:ℝ)^3))/(120*(2*Real.pi+1)*(8*lowerLambda κ)) := by
    unfold lowerCostFirst
    field_simp
    ring
  unfold lowerCostSecond
  rw [hs]
  exact div_le_div₀
    (by positivity)
    (mul_le_mul_of_nonneg_left hm (by positivity))
    (by positivity)
    (mul_le_mul_of_nonneg_left hcut (by positivity))

end BreakingResonance

#print axioms BreakingResonance.expectedProposalGradients_eq
#print axioms BreakingResonance.lowerIteration_count
#print axioms BreakingResonance.theoremTwo
