import BreakingResonance.Reversibility
import BreakingResonance.DensityLevels
import Mathlib.Probability.Kernel.Composition.MeasureCompProd

/-! The joint law of a stationary position and its update splits into the
accepted moves and the mass on the diagonal. -/
noncomputable section
namespace BreakingResonance
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

variable {S V : Type*} [MeasurableSpace S] [MeasurableSpace V]

theorem proposalKernel_compProd_eq
    (Q : S × V → S) (hQ : Measurable Q) (G : S × V → ℝ) (hG : Measurable G)
    (ν : Measure V) [IsProbabilityMeasure ν]
    (π : Measure S) [IsProbabilityMeasure π] :
    π ⊗ₘ proposalKernel Q hQ G hG ν =
      ((π.prod ν).withDensity (acceptProbability G)).map (fun z => (z.1, Q z)) +
      ((π.prod ν).withDensity (fun z => 1 - acceptProbability G z)).map
        (fun z => (z.1, z.1)) := by
  let P := proposalKernel Q hQ G hG ν
  let Ξ := ((π.prod ν).withDensity (acceptProbability G)).map (fun z => (z.1, Q z)) +
    ((π.prod ν).withDensity (fun z => 1 - acceptProbability G z)).map
      (fun z => (z.1, z.1))
  have hrect (A B : Set S) (hA : MeasurableSet A) (hB : MeasurableSet B) :
      (π ⊗ₘ P) (A ×ˢ B) = Ξ (A ×ˢ B) := by
    have hterm (F : S × V → S) (hF : Measurable F) (ξ : Measure (S × V)) :
        ξ.map (fun z => (z.1, F z)) (A ×ˢ B) =
          ∫⁻ z, A.indicator (fun _ => (1 : ℝ≥0∞)) z.1 *
            B.indicator (fun _ => (1 : ℝ≥0∞)) (F z) ∂ξ := by
      have hmap := measurable_fst.prodMk hF
      rw [Measure.map_apply hmap (hA.prod hB),
        ← lintegral_indicator_one ((hA.prod hB).preimage hmap)]
      apply lintegral_congr
      intro z
      by_cases ha : z.1 ∈ A <;> by_cases hb : F z ∈ B <;>
        simp [indicator, ha, hb]
    rw [Measure.compProd_apply_prod hA hB]
    dsimp only [P, Ξ]
    rw [Measure.add_apply, hterm Q hQ, hterm Prod.fst measurable_fst]
    exact proposalKernel_flow_split Q hQ G hG ν π A B hA hB
  have hmass : Ξ Set.univ = 1 := by
    have h := hrect Set.univ Set.univ MeasurableSet.univ MeasurableSet.univ
    simpa using h.symm
  let : IsProbabilityMeasure Ξ := ⟨hmass⟩
  exact Measure.ext_prod (fun {A B} hA hB => hrect A B hA hB)

section Gibbs

open PersistencePays

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def phaseGibbsDensity (U : E → ℝ) (z : E × E) : ℝ≥0∞ :=
  let μ := (volume : Measure E).prod (volume : Measure E)
  (ENNReal.ofReal (∫ y, Real.exp (-phaseEnergy U y) ∂μ))⁻¹ *
    ENNReal.ofReal (Real.exp (-phaseEnergy U z))

theorem phaseGibbs_eq_withDensity (U : E → ℝ) (hU : Measurable U)
    (hi : Integrable (fun x => Real.exp (-U x)) volume) :
    phaseGibbs U = ((volume : Measure E).prod volume).withDensity (phaseGibbsDensity U) := by
  rw [phaseGibbs_eq_tilted U hU hi,
    tilted_eq_smul_gibbs _ _ (measurable_phaseEnergy U hU) (phase_gibbs_integrable U hi)]
  symm
  exact withDensity_smul _ ((measurable_phaseEnergy U hU).neg.exp.ennreal_ofReal)

theorem phaseGibbsDensity_measurable (U : E → ℝ) (hU : Measurable U) :
    Measurable (phaseGibbsDensity U) := by
  unfold phaseGibbsDensity
  exact measurable_const.mul ((measurable_phaseEnergy U hU).neg.exp.ennreal_ofReal)

theorem phaseGibbsDensity_ne_top (U : E → ℝ)
    (hi : Integrable (fun x => Real.exp (-U x)) volume) (z : E × E) :
    phaseGibbsDensity U z ≠ ∞ := by
  unfold phaseGibbsDensity
  apply ENNReal.mul_ne_top _ ENNReal.ofReal_ne_top
  rw [ne_eq, ENNReal.inv_eq_top, ENNReal.ofReal_eq_zero]
  exact not_le_of_gt (integral_exp_pos (phase_gibbs_integrable U hi))

theorem fixedVerletKernel_compProd_density (U : E → ℝ) (hU : Measurable U)
    (hi : Integrable (fun x => Real.exp (-U x)) volume)
    (g : E → E) (hg : Measurable g) (h : ℝ) (j : ℕ) :
    let μ := (volume : Measure E).prod (volume : Measure E)
    let p := phaseGibbsDensity U
    let F := fun z => trajectory g h z j
    let a := acceptedWeight p F
    positionGibbs U ⊗ₘ fixedVerletKernel U hU g hg h j =
      (μ.withDensity a).map (fun z => (z.1, (F z).1)) +
        (μ.withDensity (fun z => p z - a z)).map (fun z => (z.1, z.1)) := by
  dsimp only
  let : IsProbabilityMeasure (positionGibbs U) := isProbabilityMeasure_tilted hi
  let μ := (volume : Measure E).prod (volume : Measure E)
  let p := phaseGibbsDensity U
  let F := fun z => trajectory g h z j
  let a := acceptedWeight p F
  let G := fun z => phaseEnergy U z - phaseEnergy U (F z)
  let α := acceptProbability G
  have hp := phaseGibbsDensity_measurable U hU
  have hF : Measurable F := (trajectory_measurePreserving g hg h j).measurable
  have hG : Measurable G := (measurable_phaseEnergy U hU).sub
    ((measurable_phaseEnergy U hU).comp hF)
  have hα : Measurable α := (measurable_const.min hG.exp).ennreal_ofReal
  have hβ : Measurable (fun z => 1 - α z) := measurable_const.sub hα
  have ha (z : E × E) : p z * α z = a z := by
    dsimp only [p, a, α, G, phaseGibbsDensity, acceptedWeight, acceptProbability]
    rw [mul_assoc, gibbs_acceptance_identity, mul_min]
  have hb (z : E × E) : p z * (1 - α z) = p z - a z := by
    rw [ENNReal.mul_sub (fun _ _ => phaseGibbsDensity_ne_top U hi z), mul_one, ha]
  unfold fixedVerletKernel
  rw [proposalKernel_compProd_eq]
  change ((phaseGibbs U).withDensity α).map (fun z => (z.1, (F z).1)) +
      ((phaseGibbs U).withDensity (fun z => 1 - α z)).map (fun z => (z.1, z.1)) =
    (μ.withDensity a).map (fun z => (z.1, (F z).1)) +
      (μ.withDensity (fun z => p z - a z)).map (fun z => (z.1, z.1))
  rw [phaseGibbs_eq_withDensity U hU hi, ← withDensity_mul μ hp hα,
    ← withDensity_mul μ hp hβ]
  rw [show p * α = a from funext ha,
    show p * (fun z => 1 - α z) = (fun z => p z - a z) from funext hb]

set_option maxHeartbeats 1200000 in
/-- For a fixed count, the quadratic form of the position kernel is the
signed integral over density levels plus the rejected diagonal part. -/
theorem fixedVerletKernel_quadratic_levels (U : E → ℝ) (hU : Measurable U)
    (hi : Integrable (fun x => Real.exp (-U x)) volume)
    (g : E → E) (hg : Measurable g) (h : ℝ) (j : ℕ)
    (f : E → ℝ) (hf : Measurable f) (hf₂ : MemLp f 2 (positionGibbs U)) :
    let μ := (volume : Measure E).prod (volume : Measure E)
    let p := phaseGibbsDensity U
    let F := fun z => trajectory g h z j
    let a := acceptedWeight p F
    (∫ z : E × E, f z.1 * f z.2 ∂(positionGibbs U ⊗ₘ fixedVerletKernel U hU g hg h j)) =
      (∫ u : ℝ, ∫ z, (Ioc 0 (p z).toReal).indicator (1 : ℝ → ℝ) u *
        (Ioc 0 (p (F z)).toReal).indicator (1 : ℝ → ℝ) u * (f z.1 * f (F z).1) ∂μ) +
      (∫ z, f z.1 ^ 2 ∂μ.withDensity (fun z => p z - a z)) := by
  dsimp only
  let μ := (volume : Measure E).prod (volume : Measure E)
  let p := phaseGibbsDensity U
  let F := fun z => trajectory g h z j
  let a := acceptedWeight p F
  let A := fun z : E × E => (z.1, (F z).1)
  let D := fun z : E × E => (z.1, z.1)
  let R := fun z => p z - a z
  let G := fun z : E × E => f z.1 * f z.2
  let fsharp := f ∘ (Prod.fst : E × E → E)
  have hF := trajectory_measurePreserving g hg h j
  have hfm : Measurable fsharp := hf.comp measurable_fst
  have hAm : Measurable A := measurable_fst.prodMk hF.measurable.fst
  have hDm : Measurable D := measurable_fst.prodMk measurable_fst
  have hGm : Measurable G := (hf.comp measurable_fst).mul (hf.comp measurable_snd)
  have hp := phaseGibbsDensity_measurable U hU
  have hp₀ := phaseGibbsDensity_ne_top U hi
  have ham : Measurable a := hp.min (hp.comp hF.measurable)
  have ha₀ : ∀ᵐ z ∂μ, a z < ∞ :=
    Filter.Eventually.of_forall (fun z =>
      (min_le_left (p z) (p (F z))).trans_lt (lt_top_iff_ne_top.mpr (hp₀ z)))
  have hμ : phaseGibbs U = μ.withDensity p := phaseGibbs_eq_withDensity U hU hi
  have hfsharp : MemLp fsharp 2 (μ.withDensity p) := by
    rw [← hμ]
    exact hf₂.comp_measurePreserving measurePreserving_fst
  have hacc := acceptedWeight_integrable_product μ p hp₀ hp F hF fsharp hfm hfsharp
  have hacc' : Integrable (G ∘ A) (μ.withDensity a) :=
    (integrable_withDensity_iff_integrable_smul' ham ha₀).mpr hacc
  have hrej : Integrable (fun z => f z.1^2) (μ.withDensity R) := by
    apply ((memLp_two_iff_integrable_sq hfm.aestronglyMeasurable).mp hfsharp).mono_measure
    apply withDensity_mono
    exact Filter.Eventually.of_forall (fun z => tsub_le_self)
  have hrej' : Integrable (G ∘ D) (μ.withDensity R) := by
    change Integrable (fun z => f z.1 * f z.1) (μ.withDensity R)
    simpa only [pow_two] using hrej
  rw [fixedVerletKernel_compProd_density U hU hi g hg h j]
  change (∫ z, G z ∂((μ.withDensity a).map A + (μ.withDensity R).map D)) = _
  rw [integral_add_measure
      ((integrable_map_measure hGm.aestronglyMeasurable hAm.aemeasurable).2 hacc')
      ((integrable_map_measure hGm.aestronglyMeasurable hDm.aemeasurable).2 hrej'),
    integral_map hAm.aemeasurable hGm.aestronglyMeasurable,
    integral_map hDm.aemeasurable hGm.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul ham ha₀]
  have haEq := integral_acceptedWeight_levels μ p hp₀ hp F hF.measurable
    (fun z => fsharp z * fsharp (F z)) (hfm.mul (hfm.comp hF.measurable)) hacc
  change (∫ z, (a z).toReal * (fsharp z * fsharp (F z)) ∂μ) +
      (∫ z, f z.1 * f z.1 ∂μ.withDensity R) = _
  rw [← haEq]
  simp only [fsharp, Function.comp_apply, pow_two]
  rfl

end Gibbs

end BreakingResonance

#print axioms BreakingResonance.proposalKernel_compProd_eq

#print axioms BreakingResonance.fixedVerletKernel_compProd_density

#print axioms BreakingResonance.fixedVerletKernel_quadratic_levels
