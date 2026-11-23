import BreakingResonance.RandomizedKernel

/-! The distribution of floor(tau/h) plus an independent fair Bernoulli
variable, and its first moment. These statements count every integration
stage. They do not establish the mixing-time hypotheses in Corollary 1. -/
namespace BreakingResonance
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

def roundedDurationLaw (h : ℝ) (ρ : Measure ℝ) : Measure ℕ :=
  (1/2 : ℝ≥0∞) • ρ.map (fun τ => Nat.floor (τ/h)) +
    (1/2 : ℝ≥0∞) • ρ.map (fun τ => Nat.floor (τ/h) + 1)

theorem measurable_floorDuration (h : ℝ) :
    Measurable (fun τ : ℝ => Nat.floor (τ/h)) := by fun_prop

theorem measurable_succFloorDuration (h : ℝ) :
    Measurable (fun τ : ℝ => Nat.floor (τ/h) + 1) := by fun_prop

instance roundedDurationLaw_probability (h : ℝ) (ρ : Measure ℝ)
    [IsProbabilityMeasure ρ] : IsProbabilityMeasure (roundedDurationLaw h ρ) where
  measure_univ := by
    simp [roundedDurationLaw, Measure.map_apply (measurable_floorDuration h)
      MeasurableSet.univ, Measure.map_apply (measurable_succFloorDuration h)
      MeasurableSet.univ]
    rw [← two_mul, ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]

theorem integrable_floorDuration (h : ℝ) (hh : 0 < h) (ρ : Measure ℝ)
    (hτ : Integrable (fun τ : ℝ => τ) ρ) (hpos : ∀ᵐ τ ∂ρ, 0 ≤ τ) :
    Integrable (fun τ : ℝ => (Nat.floor (τ/h) : ℝ)) ρ := by
  apply (hτ.div_const h).mono'
    (((measurable_of_countable (fun j : ℕ => (j : ℝ))).comp
      (measurable_floorDuration h)).aestronglyMeasurable)
  filter_upwards [hpos] with τ hτpos
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
  exact Nat.floor_le (div_nonneg hτpos hh.le)

theorem roundedDuration_integrable_mean (h : ℝ) (hh : 0 < h)
    (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    (hτ : Integrable (fun τ : ℝ => τ) ρ) (hpos : ∀ᵐ τ ∂ρ, 0 ≤ τ) :
    Integrable (fun j : ℕ => (j : ℝ)) (roundedDurationLaw h ρ) ∧
    (∫ j : ℕ, (j : ℝ) ∂roundedDurationLaw h ρ) =
      (∫ τ : ℝ, (Nat.floor (τ/h) : ℝ) ∂ρ) + 1/2 := by
  have hf := integrable_floorDuration h hh ρ hτ hpos
  have hf1 : Integrable (fun τ : ℝ => ((Nat.floor (τ/h) + 1 : ℕ) : ℝ)) ρ := by
    simpa using hf.add (integrable_const (1 : ℝ))
  have hj : AEStronglyMeasurable (fun j : ℕ => (j : ℝ))
      (ρ.map (fun τ => Nat.floor (τ/h))) := by fun_prop
  have hj1 : AEStronglyMeasurable (fun j : ℕ => (j : ℝ))
      (ρ.map (fun τ => Nat.floor (τ/h) + 1)) := by fun_prop
  have hmap := (integrable_map_measure hj (measurable_floorDuration h).aemeasurable).mpr hf
  have hmap1 := (integrable_map_measure hj1 (measurable_succFloorDuration h).aemeasurable).mpr hf1
  have hc : (1/2 : ℝ≥0∞) ≠ ∞ := by norm_num
  refine ⟨hmap.smul_measure hc |>.add_measure (hmap1.smul_measure hc), ?_⟩
  rw [roundedDurationLaw, integral_add_measure (hmap.smul_measure hc) (hmap1.smul_measure hc)]
  rw [integral_smul_measure, integral_smul_measure,
    integral_map (measurable_floorDuration h).aemeasurable hj,
    integral_map (measurable_succFloorDuration h).aemeasurable hj1]
  simp only [Nat.cast_add, Nat.cast_one, integral_add hf (integrable_const (1 : ℝ)),
    integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
  norm_num
  ring

theorem roundedDuration_mean_bounds (h : ℝ) (hh : 0 < h)
    (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    (hτ : Integrable (fun τ : ℝ => τ) ρ) (hpos : ∀ᵐ τ ∂ρ, 0 ≤ τ) :
    (∫ τ : ℝ, τ ∂ρ)/h - 1/2 ≤ ∫ j : ℕ, (j : ℝ) ∂roundedDurationLaw h ρ ∧
    (∫ j : ℕ, (j : ℝ) ∂roundedDurationLaw h ρ) ≤ (∫ τ : ℝ, τ ∂ρ)/h + 1/2 := by
  rw [(roundedDuration_integrable_mean h hh ρ hτ hpos).2]
  have hf := integrable_floorDuration h hh ρ hτ hpos
  have hupper := integral_mono_ae hf (hτ.div_const h) (by
    filter_upwards [hpos] with τ hτpos
    exact Nat.floor_le (div_nonneg hτpos hh.le))
  have hlower := integral_mono_ae ((hτ.div_const h).sub (integrable_const (1 : ℝ))) hf
    (Filter.Eventually.of_forall fun τ => by
      change τ/h - 1 ≤ (Nat.floor (τ/h) : ℝ)
      linarith [Nat.lt_floor_add_one (τ/h)])
  change (∫ τ : ℝ, τ/h - 1 ∂ρ) ≤ _ at hlower
  rw [integral_div] at hupper
  rw [integral_sub (hτ.div_const h) (integrable_const (1 : ℝ)), integral_div] at hlower
  simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul] at hlower
  constructor <;> linarith

/-- The actual position kernel with the rounding rule of Algorithm 1. -/
def roundedVerletKernel {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (U : E → ℝ) (hU : Measurable U) (g : E → E) (hg : Measurable g)
    (h : ℝ) (ρ : Measure ℝ) : Kernel E E :=
  randomizedVerletKernel U hU g hg h (roundedDurationLaw h ρ)

instance roundedVerletKernel_markov {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (U : E → ℝ) (hU : Measurable U) (g : E → E) (hg : Measurable g)
    (h : ℝ) (ρ : Measure ℝ) [IsProbabilityMeasure ρ] :
    IsMarkovKernel (roundedVerletKernel U hU g hg h ρ) := by
  unfold roundedVerletKernel
  infer_instance

theorem expected_stage_count {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (J : ℕ → Ω → ℕ)
    (n : ℕ) (Cinit meanJ : ℝ)
    (hJ : ∀ k < n, Integrable (fun ω => (J k ω : ℝ)) μ)
    (hmean : ∀ k < n, (∫ ω, (J k ω : ℝ) ∂μ) = meanJ) :
    (∫ ω, Cinit + 1 + ∑ k ∈ Finset.range n, (J k ω : ℝ) ∂μ) =
      Cinit + 1 + (n : ℝ) * meanJ := by
  rw [integral_add (integrable_const (Cinit+1)) (integrable_finsetSum _
    (fun k hk => hJ k (Finset.mem_range.mp hk)))]
  rw [integral_finsetSum _ (fun k hk => hJ k (Finset.mem_range.mp hk))]
  simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
  simp_rw [Finset.sum_congr rfl (fun k hk => hmean k (Finset.mem_range.mp hk))]
  simp

end
end BreakingResonance
