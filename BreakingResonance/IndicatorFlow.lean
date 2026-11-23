import BreakingResonance.MarkovL2

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace BreakingResonance

variable {S : Type*} [MeasurableSpace S]

theorem indicator_one_memLp (π : Measure S) [IsProbabilityMeasure π]
    {A : Set S} (hA : MeasurableSet A) : MemLp (A.indicator (fun _ => (1:ℝ))) 2 π :=
  (memLp_const (1:ℝ)).indicator hA

/-- The quadratic form of a set indicator reads off the stationary exit flow. -/
theorem indicator_kernel_flow (π : Measure S) [IsProbabilityMeasure π]
    (P : Kernel S S) [IsMarkovKernel P] {A : Set S} (hA : MeasurableSet A) :
    let f := A.indicator (fun _ => (1:ℝ))
    (∫ x, (f x)^2 ∂π)-kernelQuadratic π P f = (π ⊗ₘ P).real (A×ˢ Aᶜ) := by
  let f := A.indicator (fun _ : S => (1:ℝ))
  let ν := π ⊗ₘ P
  have hf (x : S) : (f x)^2 = f x := by
    by_cases hx : x ∈ A <;> simp [f,hx]
  have hm (z : S×S) : f z.1*f z.2 = (A×ˢ A).indicator (fun _ => (1:ℝ)) z := by
    by_cases h₁ : z.1 ∈ A <;> by_cases h₂ : z.2 ∈ A <;> simp [f,h₁,h₂]
  have hfst : ν.real (A ×ˢ univ) = π.real A := by
    rw [Measure.real,Measure.compProd_apply_prod hA MeasurableSet.univ]
    simp [Measure.real]
  have hsplit : ν.real (A ×ˢ A) + ν.real (A ×ˢ Aᶜ) = ν.real (A ×ˢ univ) := by
    rw [← measureReal_union (by
      refine disjoint_left.mpr ?_
      exact fun z hz hz' => hz'.2 hz.2) (hA.prod hA.compl)]
    congr 1
    ext z
    by_cases hz : z.2 ∈ A <;> simp [hz]
  change (∫ x, (f x)^2 ∂π)-kernelQuadratic π P f = _
  simp_rw [hf]
  unfold kernelQuadratic
  simp_rw [hm]
  unfold f
  rw [integral_indicator hA, integral_indicator (hA.prod hA),
    setIntegral_const,setIntegral_const,smul_eq_mul,smul_eq_mul,mul_one,mul_one]
  change π.real A - ν.real (A×ˢ A) = ν.real (A×ˢ Aᶜ)
  linarith only [hfst,hsplit]

end BreakingResonance

#print axioms BreakingResonance.indicator_kernel_flow
