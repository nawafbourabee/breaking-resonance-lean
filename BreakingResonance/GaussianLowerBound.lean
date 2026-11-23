import BreakingResonance.CrossingPathLaw
import BreakingResonance.IndependentCounts
import BreakingResonance.GaussianKernelCrossing

noncomputable section

open MeasureTheory ProbabilityTheory Set PersistencePays
open scoped ENNReal ProbabilityTheory

namespace BreakingResonance

section Markov

variable {S : Type*} [MeasurableSpace S]

theorem invariant_domination_iterates (P : Kernel S S) (π ν : Measure S)
    (hP : Kernel.Invariant P π) (hν : ν ≤ (2:ℝ≥0∞) • π) (n : ℕ) :
    evolve (fun _ => P) ν n ≤ (2:ℝ≥0∞) • π := by
  induction n with
  | zero => exact hν
  | succ n ih =>
    rw [evolve_succ]
    have h : (P ∘ₘ evolve (fun _ => P) ν n) ≤ P ∘ₘ ((2:ℝ≥0∞) • π) := by
      apply Measure.le_iff.mpr
      intro A hA
      rw [Measure.bind_apply hA P.aemeasurable,Measure.bind_apply hA P.aemeasurable]
      exact lintegral_mono' ih le_rfl
    rw [Measure.comp_smul,hP.def] at h
    exact h

theorem invariant_domination_exit (P : Kernel S S) [IsMarkovKernel P]
    (π ν : Measure S) [IsProbabilityMeasure ν] (hP : Kernel.Invariant P π)
    (hν : ν ≤ (2:ℝ≥0∞) • π) {A : Set S} (hA : MeasurableSet A) (hνA : ν Aᶜ = 0)
    {B : ℝ≥0∞} (hcross : stationaryCrossing π P A ≤ B) (n : ℕ) :
    (evolve (fun _ => P) ν n) Aᶜ ≤ ((n:ℝ≥0∞)*2)*B := by
  apply (markovPathLaw_exit_le_crossing_sum P ν hA hνA n).trans
  calc
    _ ≤ ∑ _i ∈ Finset.range n, (2:ℝ≥0∞)*B := by
      apply Finset.sum_le_sum
      intro i _
      have h := invariant_domination_iterates P π ν hP hν i
      have hm := Measure.restrict_mono (show A ⊆ A from subset_rfl) h
      have hin := lintegral_mono' (f := fun x => P x Aᶜ) hm le_rfl
      rw [Measure.restrict_smul,lintegral_smul_measure,smul_eq_mul] at hin
      exact hin.trans (mul_le_mul_right hcross _)
    _ = _ := by simp [nsmul_eq_mul,mul_assoc]

end Markov

def gaussianWarmStart (m L : ℝ) : Measure (EuclideanSpace ℝ (Fin 2)) :=
  (2:ℝ≥0∞) • (positionGibbs (diagonalGaussianPotential m L)).restrict gaussianSlowHalfspace

/-- Expected gradient evaluations in the count identity of Corollary 1, with an arbitrary count
law. The initial contribution is the cost of generating the starting
position, followed by one evaluation to initialize the stored gradient. -/
def gaussianExpectedGradients (lawJ : Measure ℕ) (Cinit : ℝ) (n : ℕ) : ℝ :=
  ∫ J : Fin n → ℕ, Cinit+1+∑ i, (J i:ℝ) ∂Measure.pi (fun _ => lawJ)

theorem gaussianExpectedGradients_eq (lawJ : Measure ℕ) [IsProbabilityMeasure lawJ]
    (hJ : Integrable (fun j : ℕ => (j:ℝ)) lawJ) (Cinit : ℝ) (n : ℕ) :
    gaussianExpectedGradients lawJ Cinit n = Cinit+1+(n:ℝ)*(∫ j : ℕ, (j:ℝ) ∂lawJ) := by
  obtain ⟨hI,hEq⟩ := independentCountSum lawJ hJ n
  unfold gaussianExpectedGradients
  rw [integral_add (integrable_const _) hI,hEq]
  simp

set_option maxHeartbeats 800000 in
/-- Proposition B.1, for the actual Metropolis-adjusted position kernel
with any independent count law of positive finite mean. -/
theorem gaussianGradientLowerBound (m L h : ℝ) (hm : 0 < m) (hmL : m ≤ L)
    (hh : 0 < h) (hhL : h*Real.sqrt L ≤ 1) (lawJ : Measure ℕ) [IsProbabilityMeasure lawJ]
    (hJ : Integrable (fun j : ℕ => (j:ℝ)) lawJ) (_hJpos : 0 < ∫ j : ℕ, (j:ℝ) ∂lawJ)
    (Cinit : ℝ) (hInit : 0 ≤ Cinit) (n : ℕ) :
    let U := diagonalGaussianPotential m L
    let π := positionGibbs U
    let g := diagonalGaussianForce m L
    let P := randomizedVerletKernel U (diagonalGaussianPotential_measurable m L)
      g (diagonalGaussianForce_measurable hm hmL) h lawJ
    totalVariation (evolve (fun _ => P) (gaussianWarmStart m L) n) π ≤ 1/4 →
    (n:ℝ)*(∫ j : ℕ, (j:ℝ) ∂lawJ) ≤ gaussianExpectedGradients lawJ Cinit n ∧
    3*Real.pi/(16*h*Real.sqrt m) ≤ (n:ℝ)*(∫ j : ℕ, (j:ℝ) ∂lawJ) ∧
    (3*Real.pi/16)*Real.sqrt (L/m) ≤ 3*Real.pi/(16*h*Real.sqrt m) := by
  let U := diagonalGaussianPotential m L
  let g := diagonalGaussianForce m L
  let hU := diagonalGaussianPotential_measurable m L
  let hg := diagonalGaussianForce_measurable hm hmL
  let P := randomizedVerletKernel U hU g hg h lawJ
  let π := positionGibbs U
  let A := gaussianSlowHalfspace
  let ν := gaussianWarmStart m L
  let EJ := ∫ j : ℕ, (j:ℝ) ∂lawJ
  let c := 2/(3*Real.pi)*(h*Real.sqrt m)
  have : IsMarkovKernel P := randomizedVerletKernel_markov _ _ _ _ _ _
  have : IsProbabilityMeasure π := isProbabilityMeasure_tilted
    (diagonalGaussianPotential_integrable hm hmL)
  have hA := gaussianSlowHalfspace_measurable
  have hAhalf : π A = 1/2 := gaussianSlowHalfspace_mass hm hmL
  have : IsProbabilityMeasure ν := by
    refine ⟨?_⟩
    change ((2:ℝ≥0∞) • π.restrict A) univ = _
    rw [Measure.smul_apply,Measure.restrict_apply_univ,hAhalf,smul_eq_mul,one_div,
      ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]
  have hν : ν ≤ (2:ℝ≥0∞) • π := by
    change (2:ℝ≥0∞) • π.restrict A ≤ (2:ℝ≥0∞) • π
    exact smul_le_smul_left (2:ℝ≥0∞) Measure.restrict_le_self
  have hνA : ν Aᶜ = 0 := by
    change ((2:ℝ≥0∞) • π.restrict A) Aᶜ = _
    rw [Measure.smul_apply,Measure.restrict_apply hA.compl,compl_inter_self,measure_empty,smul_zero]
  have hinv := (randomizedVerletKernel_reversible U hU (diagonalGaussianPotential_integrable hm hmL)
    g hg h lawJ).invariant
  have hC : stationaryCrossing π P A ≤ ENNReal.ofReal (c*EJ) :=
    gaussianMixedKernel_crossing hm hmL hh hhL lawJ hJ
  have hexit := invariant_domination_exit P π ν hinv hν hA hνA hC n
  have hac : π.real Aᶜ = 1/2 := by
    rw [Measure.real,prob_compl_eq_one_sub hA,hAhalf]
    norm_num
  dsimp only
  intro hTV
  let μ := evolve (fun _ => P) ν n
  have hTV' : totalVariation π μ ≤ 1/4 := by
    have he : totalVariation π μ = totalVariation μ π := by
      simp only [totalVariation,abs_sub_comm (π.real _) (μ.real _)]
    rw [he]
    exact hTV
  have htest := (event_le_totalVariation π μ Aᶜ hA.compl).trans hTV'
  have hμ : 1/4 ≤ μ.real Aᶜ := by
    have hl := ENNReal.toReal_mono (by norm_num : (1/4:ℝ≥0∞) ≠ ∞) htest
    by_cases hpos : 0 ≤ π.real Aᶜ-μ.real Aᶜ
    · rw [ENNReal.toReal_ofReal hpos,hac] at hl
      norm_num at hl
      linarith only [hl]
    · rw [hac] at hpos
      linarith only [lt_of_not_ge hpos]
  have hEJ : 0 ≤ EJ := _hJpos.le
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hx : μ.real Aᶜ ≤ (n:ℝ)*2*(c*EJ) := by
    have he := ENNReal.toReal_mono (by finiteness) hexit
    rwa [ENNReal.toReal_mul,ENNReal.toReal_mul,ENNReal.toReal_natCast,ENNReal.toReal_ofNat,
      ENNReal.toReal_ofReal (mul_nonneg hc hEJ)] at he
  refine ⟨?_,?_,?_⟩
  · rw [gaussianExpectedGradients_eq _ hJ]
    linarith only [hInit]
  · change 3*Real.pi/(16*h*Real.sqrt m) ≤ (n:ℝ)*EJ
    apply (div_le_iff₀ (by positivity : 0 < 16*h*Real.sqrt m)).mpr
    have hhyp := (mul_le_mul_of_nonneg_right (hμ.trans hx)
      (show 0 ≤ 12*Real.pi by positivity))
    have hform : ↑n*2*(c*EJ)*(12*Real.pi) = (n:ℝ)*EJ*(16*h*Real.sqrt m) := by
      dsimp [c]
      field_simp [Real.pi_ne_zero]
      ring
    rw [hform] at hhyp
    linarith only [hhyp]
  · apply (le_div_iff₀ (by positivity : 0 < 16*h*Real.sqrt m)).mpr
    have he : Real.sqrt (L/m)*Real.sqrt m = Real.sqrt L := by
      rw [Real.sqrt_div (hm.le.trans hmL),div_mul_cancel₀ _ (Real.sqrt_pos.mpr hm).ne']
    calc
      _ = 3*Real.pi*h*(Real.sqrt (L/m)*Real.sqrt m) := by ring
      _ = 3*Real.pi*(h*Real.sqrt L) := by rw [he]; ring
      _ ≤ _ := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hhL (show 0 ≤ 3*Real.pi by positivity)

end BreakingResonance

#print axioms BreakingResonance.invariant_domination_iterates
#print axioms BreakingResonance.invariant_domination_exit
#print axioms BreakingResonance.gaussianExpectedGradients_eq
#print axioms BreakingResonance.gaussianGradientLowerBound
