import BreakingResonance.LowerProductGibbs

noncomputable section

open MeasureTheory Set PersistencePays
open scoped ENNReal

namespace BreakingResonance

private theorem half_energy_exp_factor {a b : ℝ} (z : ℝ×ℝ) :
    Real.exp (-phaseEnergy (fastPotential a b) z/2) =
      Real.exp (-fastPotential (a/2) (b/2) z.1)*Real.exp (-(1/4:ℝ)*z.2^2) := by
  rw [← Real.exp_add,phaseEnergy_eq_norm,Real.norm_eq_abs,sq_abs]
  congr 1
  unfold fastPotential
  split_ifs <;> ring

private theorem normalizer_half_coeff (c : ℝ) :
    Real.sqrt (Real.pi/(c/2/2)) = Real.sqrt 2*Real.sqrt (Real.pi/(c/2)) := by
  rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
  congr 1
  ring

theorem scalar_phase_exp_moment {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    let U := fastPotential a b
    let H := phaseEnergy U
    Integrable (fun z => Real.exp (H z/2)) (phaseGibbs U) ∧
      (∫ z, Real.exp (H z/2) ∂(phaseGibbs U)) = 2 := by
  let U := fastPotential a b
  let H := phaseEnergy U
  let μ : Measure (ℝ×ℝ) := (volume : Measure ℝ).prod volume
  have hi := fastPotential_gibbs_integrable ha hab
  have hI := phase_gibbs_integrable U hi
  have hμ := phaseGibbs_eq_tilted U (fastPotential_continuous _ _).measurable hi
  have hhalf : Integrable (fun z => Real.exp (-H z/2)) μ := by
    simp_rw [H,U,half_energy_exp_factor]
    exact (fastPotential_gibbs_integrable (half_pos ha) (by linarith only [hab])).mul_prod
      (integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1/4))
  change Integrable (fun z => Real.exp (H z/2)) (phaseGibbs U) ∧ _
  rw [hμ]
  refine ⟨?_,?_⟩
  · apply (integrable_tilted_iff hI _).mpr
    convert hhalf using 1
    funext z
    rw [smul_eq_mul,← Real.exp_add]
    congr 1
    ring
  · rw [integral_exp_tilted]
    have hE : (fun z => Real.exp ((-H+(fun y => H y/2)) z)) = fun z => Real.exp (-H z/2) := by
      funext z
      simp only [Pi.add_apply,Pi.neg_apply]
      congr 1
      ring
    rw [hE]
    have hZ : 0 < ∫ z, Real.exp (-H z) ∂μ := integral_exp_pos hI
    apply (div_eq_iff hZ.ne').mpr
    simp_rw [H,U,half_energy_exp_factor]
    rw [integral_prod_mul (fun x => Real.exp (-fastPotential (a/2) (b/2) x))
        (fun v => Real.exp (-(1/4:ℝ)*v^2)),
      phase_gibbs_normalizer (fastPotential a b), fastPotential_normalizer (half_pos ha) (by linarith only [hab]),
      fastPotential_normalizer ha hab,integral_gaussian (1/4)]
    have hV : (∫ v : ℝ, Real.exp (-kineticPotential v)) = Real.sqrt (Real.pi/(1/2)) := by
      rw [← integral_gaussian (1/2)]
      congr 1
      funext v
      rw [kineticPotential,Real.norm_eq_abs,sq_abs]
      congr 1
      ring
    rw [hV,normalizer_half_coeff a,normalizer_half_coeff b,
      show Real.sqrt (Real.pi/(1/4)) = Real.sqrt 2*Real.sqrt (Real.pi/(1/2)) by
        rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
        congr 1
        ring]
    ring_nf
    rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    ring

theorem separable_phase_exp_moment {ι : Type*} [Fintype ι] (a b : ι → ℝ)
    (ha : ∀ i, 0 < a i) (hab : ∀ i, a i ≤ b i) :
    let U := separablePotential a b
    let H := phaseEnergy U
    Integrable (fun z => Real.exp (H z/2)) (phaseGibbs U) ∧
      (∫ z, Real.exp (H z/2) ∂(phaseGibbs U)) = 2^(Fintype.card ι) := by
  let U := separablePotential a b
  let H := phaseEnergy U
  let μ (i : ι) := phaseGibbs (fastPotential (a i) (b i))
  let f (i : ι) (z : ℝ×ℝ) := Real.exp (phaseEnergy (fastPotential (a i) (b i)) z/2)
  let e := phaseCoordinates ι
  have he : MeasurePreserving e (phaseGibbs U) (Measure.pi μ) :=
    ⟨e.measurable,separablePhaseGibbs_coordinates a b ha hab⟩
  have hi (i : ι) : Integrable (f i) (μ i) := (scalar_phase_exp_moment (ha i) (hab i)).1
  have hM (i : ι) : (∫ z, f i z ∂(μ i)) = 2 := (scalar_phase_exp_moment (ha i) (hab i)).2
  have hf : (fun z => Real.exp (H z/2)) = (fun y : ι → ℝ×ℝ => ∏ i, f i (y i)) ∘ e := by
    funext z
    simp only [H,U,separableEnergy,Finset.sum_div,Real.exp_sum,Function.comp_apply,
      e,phaseCoordinates_apply,f]
  change Integrable (fun z => Real.exp (H z/2)) (phaseGibbs U) ∧
    (∫ z, Real.exp (H z/2) ∂(phaseGibbs U)) = _
  rw [hf]
  refine ⟨(he.integrable_comp_emb e.measurableEmbedding).mpr (Integrable.fintype_prod hi),?_⟩
  change (∫ x, (∏ i, f i ((e x) i)) ∂(phaseGibbs U)) = _
  rw [he.integral_comp e.measurableEmbedding (fun y => ∏ i, f i (y i)),
    integral_fintype_prod_eq_prod f]
  simp_rw [hM]
  simp

end BreakingResonance

#print axioms BreakingResonance.scalar_phase_exp_moment
#print axioms BreakingResonance.separable_phase_exp_moment
