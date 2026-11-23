import BreakingResonance.GaussianCrossingMeasure
import BreakingResonance.LowerProductGibbs
import BreakingResonance.LowerWarmStart

noncomputable section

open MeasureTheory ProbabilityTheory Set PersistencePays
open scoped ENNReal

namespace BreakingResonance

def diagonalGaussianCurvature (m L : ℝ) (i : Fin 2) : ℝ := if i = 0 then m else L

def diagonalGaussianPotential (m L : ℝ) : EuclideanSpace ℝ (Fin 2) → ℝ :=
  separablePotential (diagonalGaussianCurvature m L) (diagonalGaussianCurvature m L)

def diagonalGaussianForce (m L : ℝ) : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
  separableForce (diagonalGaussianCurvature m L) (diagonalGaussianCurvature m L)

theorem diagonalGaussianPotential_eq (m L : ℝ) (x : EuclideanSpace ℝ (Fin 2)) :
    diagonalGaussianPotential m L x = m*(x 0)^2/2+L*(x 1)^2/2 := by
  unfold diagonalGaussianPotential separablePotential
  rw [Fin.sum_univ_two]
  simp [diagonalGaussianCurvature,fastPotential]

theorem diagonalGaussianPotential_integrable {m L : ℝ} (hm : 0 < m) (hmL : m ≤ L) :
    Integrable (fun x => Real.exp (-diagonalGaussianPotential m L x)) volume := by
  apply separablePotential_gibbs_integrable _ _ _ (fun _ => le_rfl)
  intro i
  unfold diagonalGaussianCurvature
  split_ifs <;> linarith only [hm,hmL]

theorem diagonalGaussianPotential_measurable (m L : ℝ) :
    Measurable (diagonalGaussianPotential m L) := by
  have h : diagonalGaussianPotential m L = fun x => m*(x 0)^2/2+L*(x 1)^2/2 :=
    funext (diagonalGaussianPotential_eq m L)
  rw [h]
  exact (((continuous_const.mul ((PiLp.proj (𝕜 := ℝ) (p := 2)
    (β := fun _ : Fin 2 => ℝ) 0).continuous.pow 2)).div_const _).add
    ((continuous_const.mul ((PiLp.proj (𝕜 := ℝ) (p := 2)
    (β := fun _ : Fin 2 => ℝ) 1).continuous.pow 2)).div_const _)).measurable

theorem diagonalGaussianForce_measurable {m L : ℝ} (hm : 0 < m) (hmL : m ≤ L) :
    Measurable (diagonalGaussianForce m L) := by
  let ℓ : NNReal := ⟨L,hm.le.trans hmL⟩
  have h : LipschitzWith ℓ (diagonalGaussianForce m L) := by
    apply separableForce_lipschitz _ _ (fun _ => le_rfl)
    · intro i
      unfold diagonalGaussianCurvature
      split_ifs <;> linarith only [hm,hmL]
    · intro i
      unfold diagonalGaussianCurvature
      split_ifs
      · exact hmL
      · exact le_rfl
  exact h.continuous.measurable

def gaussianSlowHalfspace : Set (EuclideanSpace ℝ (Fin 2)) := {x | x 0 ≤ 0}

theorem gaussianSlowHalfspace_measurable : MeasurableSet gaussianSlowHalfspace :=
  measurableSet_le ((PiLp.proj (𝕜 := ℝ) (p := 2)
    (β := fun _ : Fin 2 => ℝ) 0).continuous.measurable) measurable_const

theorem gaussianSlowPhase_projection {m L : ℝ} (hm : 0 < m) (hmL : m ≤ L) :
    MeasurePreserving (fun z : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) =>
      (z.1 0,z.2 0)) (phaseGibbs (diagonalGaussianPotential m L)) (phaseGibbs (fastPotential m m)) := by
  let c := diagonalGaussianCurvature m L
  let μ (i : Fin 2) := phaseGibbs (fastPotential (c i) (c i))
  let e := phaseCoordinates (Fin 2)
  have hc (i : Fin 2) : 0 < c i := by dsimp [c,diagonalGaussianCurvature]; split_ifs <;> linarith only [hm,hmL]
  have (i : Fin 2) : IsProbabilityMeasure (μ i) := by
    have : IsProbabilityMeasure (positionGibbs (fastPotential (c i) (c i))) :=
      isProbabilityMeasure_tilted (fastPotential_gibbs_integrable (hc i) le_rfl)
    unfold μ phaseGibbs
    infer_instance
  have he : MeasurePreserving e (phaseGibbs (diagonalGaussianPotential m L)) (Measure.pi μ) :=
    ⟨e.measurable,separablePhaseGibbs_coordinates c c hc (fun _ => le_rfl)⟩
  change MeasurePreserving ((Function.eval (0:Fin 2)) ∘ e) _ _
  have h := (measurePreserving_eval μ (0:Fin 2)).comp he
  simpa only [μ,c,diagonalGaussianCurvature,ite_true] using h

theorem scalarQuadratic_halfspace_neg {m : ℝ} (hm : 0 < m) :
    positionGibbs (fastPotential m m) (Iic 0) = 1/2 := by
  let ν := positionGibbs (fastPotential m m)
  have he : ν.map (fun x : ℝ => -x) = ν := by
    change (positionGibbs (fastPotential m m)).map (fun x : ℝ => -x) = positionGibbs (fastPotential m m)
    rw [quadratic_positionGaussian hm]
    simpa only [neg_zero] using (gaussianReal_map_neg (μ := (0:ℝ)) (v := ⟨m⁻¹,inv_nonneg.mpr hm.le⟩))
  have ha : (fun x : ℝ => -x) ⁻¹' Ici (0:ℝ) = Iic 0 := by ext; simp
  have h := Measure.map_apply (μ := ν) measurable_neg
    (measurableSet_Ici (a := (0:ℝ)))
  rw [he,ha] at h
  exact h.symm.trans (scalarQuadratic_halfspace hm)

theorem gaussianSlowHalfspace_mass {m L : ℝ} (hm : 0 < m) (hmL : m ≤ L) :
    positionGibbs (diagonalGaussianPotential m L) gaussianSlowHalfspace = 1/2 := by
  let μ := phaseGibbs (diagonalGaussianPotential m L)
  let ν := phaseGibbs (fastPotential m m)
  let F (z : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) := (z.1 0,z.2 0)
  let A := Iic (0:ℝ) ×ˢ (univ : Set ℝ)
  have hF : MeasurePreserving F μ ν := gaussianSlowPhase_projection hm hmL
  have hA : MeasurableSet A := measurableSet_Iic.prod MeasurableSet.univ
  have he : μ (gaussianSlowHalfspace ×ˢ univ) = ν A := by
    change μ (F ⁻¹' A) = _
    rw [← Measure.map_apply hF.measurable hA,hF.map_eq]
  unfold μ ν A phaseGibbs at he
  rw [Measure.prod_prod,Measure.prod_prod,measure_univ,mul_one,measure_univ,mul_one,
    scalarQuadratic_halfspace_neg hm] at he
  exact he

end BreakingResonance

#print axioms BreakingResonance.diagonalGaussianPotential_eq
#print axioms BreakingResonance.gaussianSlowPhase_projection
#print axioms BreakingResonance.gaussianSlowHalfspace_mass
