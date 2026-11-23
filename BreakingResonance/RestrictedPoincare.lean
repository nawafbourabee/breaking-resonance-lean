import BreakingResonance.BoundedMedian
import BreakingResonance.RestrictedPoincareHalf
import Mathlib.Probability.Moments.Variance

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace BreakingResonance

variable {S : Type*} [MeasurableSpace S]

/-- Weak Poincare inequality from restricted conductance, with the range
length as an upper bound on the oscillation. -/
theorem restrictedConductance_variance_le
    (π : Measure S) [IsProbabilityMeasure π] (P : Kernel S S) [IsMarkovKernel P]
    (hrev : P.IsReversible π) {s φ C : ℝ} (hs : 0 ≤ s) (hφ : 0 < φ)
    (hcond : RestrictedConductance π P s φ) {f : S → ℝ} (hf : Measurable f)
    (hlo : ∀ x, 0 ≤ f x) (hhi : ∀ x, f x ≤ C) :
    variance f π ≤ 2/φ^2*markovDirichlet π P f+2*s*C^2 := by
  obtain ⟨a,ha,hl,hr⟩ := exists_bounded_median π hf hlo hhi
  let g (x : S) := max (f x-a) 0
  let j (x : S) := max (a-f x) 0
  have hgm : Measurable g := (hf.sub measurable_const).max measurable_const
  have hjm : Measurable j := (measurable_const.sub hf).max measurable_const
  have hg₀ (x : S) : 0 ≤ g x := le_max_right _ _
  have hj₀ (x : S) : 0 ≤ j x := le_max_right _ _
  have hg₁ (x : S) : g x ≤ C-a := max_le (sub_le_sub_right (hhi x) _) (sub_nonneg.mpr ha.2)
  have hj₁ (x : S) : j x ≤ a := max_le (sub_le_self _ (hlo x)) ha.1
  have hgs : π {x | 0 < g x} ≤ 1/2 := by
    simpa only [g,lt_max_iff,lt_irrefl,or_false,sub_pos] using hr
  have hjs : π {x | 0 < j x} ≤ 1/2 := by
    simpa only [j,lt_max_iff,lt_irrefl,or_false,sub_pos] using hl
  have hg := restrictedConductance_half_square π P hrev hs hφ hcond hgm hg₀ hg₁ hgs
  have hj := restrictedConductance_half_square π P hrev hs hφ hcond hjm hj₀ hj₁ hjs
  have hmem : MemLp (fun x => f x-a) 2 π := memLp_of_bounded
    (a := -a) (b := C-a) (Filter.Eventually.of_forall fun x =>
      ⟨by linarith only [hlo x],sub_le_sub_right (hhi x) a⟩)
    (hf.sub measurable_const).aestronglyMeasurable 2
  have hcenter : variance f π ≤ ∫ x, (f x-a)^2 ∂π := by
    rw [← variance_sub_const hf.aestronglyMeasurable a,variance_eq_sub hmem]
    change (∫ x,(f x-a)^2 ∂π)-(∫ x,(f x-a) ∂π)^2 ≤ ∫ x,(f x-a)^2 ∂π
    linarith only [sq_nonneg (∫ x, (f x-a) ∂π)]
  have hsplit (x : S) : (f x-a)^2 = (g x)^2+(j x)^2 := by
    by_cases h : f x ≤ a
    · simp only [g,j,max_eq_right (sub_nonpos.mpr h),max_eq_left (sub_nonneg.mpr h)]
      ring
    · have h' : a ≤ f x := le_of_not_ge h
      simp only [g,j,max_eq_left (sub_nonneg.mpr h'),max_eq_right (sub_nonpos.mpr h')]
      ring
  have hgi : MemLp g 2 π := memLp_of_bounded
    (Filter.Eventually.of_forall fun x => ⟨hg₀ x,hg₁ x⟩) hgm.aestronglyMeasurable 2
  have hji : MemLp j 2 π := memLp_of_bounded
    (Filter.Eventually.of_forall fun x => ⟨hj₀ x,hj₁ x⟩) hjm.aestronglyMeasurable 2
  have hgis := (memLp_two_iff_integrable_sq hgi.aestronglyMeasurable).mp hgi
  have hjis := (memLp_two_iff_integrable_sq hji.aestronglyMeasurable).mp hji
  have hspint : (∫ x,(f x-a)^2 ∂π) = (∫ x,(g x)^2 ∂π)+(∫ x,(j x)^2 ∂π) := by
    simp_rw [hsplit]
    exact integral_add hgis hjis
  rw [hspint] at hcenter
  let ν := π ⊗ₘ P
  have hfst : MeasurePreserving Prod.fst ν π := ⟨measurable_fst,Measure.fst_compProd π P⟩
  have hsnd : MeasurePreserving Prod.snd ν π := kernel_snd_measurePreserving π P hrev.invariant
  have hint {l : S → ℝ} (h : MemLp l 2 π) : Integrable (fun z : S×S => (l z.1-l z.2)^2) ν :=
    (memLp_two_iff_integrable_sq ((h.comp_measurePreserving hfst).sub
      (h.comp_measurePreserving hsnd)).aestronglyMeasurable).mp
      ((h.comp_measurePreserving hfst).sub (h.comp_measurePreserving hsnd))
  have hen (z : S×S) : (g z.1-g z.2)^2+(j z.1-j z.2)^2 ≤ (f z.1-f z.2)^2 := by
    by_cases h₁ : f z.1 ≤ a <;> by_cases h₂ : f z.2 ≤ a
    · simp [g,j,max_eq_right (sub_nonpos.mpr h₁),max_eq_left (sub_nonneg.mpr h₁),
        max_eq_right (sub_nonpos.mpr h₂),max_eq_left (sub_nonneg.mpr h₂)]
      ring_nf
      exact le_rfl
    · have h₂' := le_of_not_ge h₂
      simp only [g,j,max_eq_right (sub_nonpos.mpr h₁),max_eq_left (sub_nonneg.mpr h₁),
        max_eq_left (sub_nonneg.mpr h₂'),max_eq_right (sub_nonpos.mpr h₂')]
      nlinarith only [mul_nonneg (sub_nonneg.mpr h₁) (sub_nonneg.mpr h₂')]
    · have h₁' := le_of_not_ge h₁
      simp only [g,j,max_eq_right (sub_nonpos.mpr h₂),max_eq_left (sub_nonneg.mpr h₂),
        max_eq_left (sub_nonneg.mpr h₁'),max_eq_right (sub_nonpos.mpr h₁')]
      nlinarith only [mul_nonneg (sub_nonneg.mpr h₂) (sub_nonneg.mpr h₁')]
    · have h₁' := le_of_not_ge h₁
      have h₂' := le_of_not_ge h₂
      simp [g,j,max_eq_left (sub_nonneg.mpr h₁'),max_eq_right (sub_nonpos.mpr h₁'),
        max_eq_left (sub_nonneg.mpr h₂'),max_eq_right (sub_nonpos.mpr h₂')]
  have hfLp : MemLp f 2 π := memLp_of_bounded
    (Filter.Eventually.of_forall fun x => ⟨hlo x,hhi x⟩) hf.aestronglyMeasurable 2
  have heste := integral_mono ((hint hgi).add (hint hji)) (hint hfLp) hen
  change (∫ z, (g z.1-g z.2)^2+(j z.1-j z.2)^2 ∂ν) ≤
    ∫ z, (f z.1-f z.2)^2 ∂ν at heste
  have hsum : (∫ z, (g z.1-g z.2)^2+(j z.1-j z.2)^2 ∂ν) =
    (∫ z, (g z.1-g z.2)^2 ∂ν)+(∫ z, (j z.1-j z.2)^2 ∂ν) :=
    integral_add (hint hgi) (hint hji)
  rw [hsum] at heste
  have henergy : markovDirichlet π P g+markovDirichlet π P j ≤ markovDirichlet π P f := by
    change (1/2)*(∫ z,(g z.1-g z.2)^2 ∂ν)+(1/2)*(∫ z,(j z.1-j z.2)^2 ∂ν) ≤
      (1/2)*(∫ z,(f z.1-f z.2)^2 ∂ν)
    linarith only [heste]
  have hcap : (C-a)^2+a^2 ≤ C^2 := by
    nlinarith only [mul_nonneg ha.1 (sub_nonneg.mpr ha.2)]
  have he := mul_le_mul_of_nonneg_left henergy (show 0 ≤ 2/φ^2 by positivity)
  have hc := mul_le_mul_of_nonneg_left hcap (show 0 ≤ 2*s by positivity)
  linarith only [hcenter,hg,hj,he,hc]

end BreakingResonance

#print axioms BreakingResonance.restrictedConductance_variance_le
