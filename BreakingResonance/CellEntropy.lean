import BreakingResonance.CellLaws
import BreakingResonance.FlightEntropyContinuity
import BreakingResonance.VerletQuadrature

/-! Exact endpoint cancellation in the Gibbs entropy of a Verlet free flight. -/
noncomputable section
namespace BreakingResonance
open PersistencePays MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def cellRemainder (U : E → ℝ) (g : E → E) (h σ : ℝ) (z : E×E) : ℝ :=
  U (z.1+σ • flightVelocity g h z)-U z.1-σ*⟪g z.1,flightVelocity g h z⟫

theorem flightVelocity_memLp {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (μ : Measure (E×E)) [IsProbabilityMeasure μ] (hμ : MemLp id 2 μ) (h : ℝ) :
    MemLp (flightVelocity (gradient U) h) 2 μ :=
  hμ.snd.sub ((a.gradient_memLp hμ.fst).const_smul (h/2))

theorem forceVelocity_integrable {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (μ : Measure (E×E)) [IsProbabilityMeasure μ] (hμ : MemLp id 2 μ) (h : ℝ) :
    Integrable (fun z=>⟪gradient U z.1,flightVelocity (gradient U) h z⟫) μ :=
  integrable_inner_of_memLp_two (a.gradient_memLp hμ.fst) (flightVelocity_memLp a μ hμ h)

theorem modifiedEnergy_difference_integrable {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (μ : Measure (E×E)) [IsProbabilityMeasure μ] (hμ : MemLp id 2 μ) (h : ℝ) :
    Integrable (fun z=>modifiedEnergy U (gradient U) h z-phaseEnergy U z) μ := by
  have he (z : E×E) : modifiedEnergy U (gradient U) h z-phaseEnergy U z=
      -(h^2/8)*‖gradient U z.1‖^2 := by
    simp only [modifiedEnergy,gradientCorrection,real_inner_self_eq_norm_sq]
    ring
  simp_rw [he]
  exact (a.gradient_memLp hμ.fst).integrable_norm_pow'.const_mul _

theorem cellRemainder_integrable {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (μ : Measure (E×E)) [IsProbabilityMeasure μ] (hμ : MemLp id 2 μ) (h σ : ℝ) :
    Integrable (cellRemainder U (gradient U) h σ) μ :=
  ((a.potential_integrable (hμ.fst.add ((flightVelocity_memLp a μ hμ h).const_smul σ))).sub
    (a.potential_integrable hμ.fst)).sub ((forceVelocity_integrable a μ hμ h).const_mul σ)

theorem cell_entropy_split {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (μ : Measure (E×E)) [IsProbabilityMeasure μ] (hμ : MemLp id 2 μ)
    (hK : klDiv μ (phaseGibbs U)≠∞) (h σ : ℝ) :
    (klDiv (μ.map (cellState (gradient U) h σ)) (phaseGibbs U)).toReal=
      (klDiv μ (phaseGibbs U)).toReal+
      (∫z,modifiedEnergy U (gradient U) h z-phaseEnergy U z ∂μ)+
      (σ-h/2)*(∫z,⟪gradient U z.1,flightVelocity (gradient U) h z⟫ ∂μ)+
      (∫z,cellRemainder U (gradient U) h σ z ∂μ) := by
  have hb := (cell_entropy_change a μ hμ hK h σ).2
  have he (z : E×E) : phaseEnergy U (cellState (gradient U) h σ z)-phaseEnergy U z=
      (modifiedEnergy U (gradient U) h z-phaseEnergy U z)+
      (σ-h/2)*⟪gradient U z.1,flightVelocity (gradient U) h z⟫+
      cellRemainder U (gradient U) h σ z := by
    rw [cellState_energy_identity]
    dsimp only [cellRemainder]
    ring
  simp_rw [he] at hb
  have hi := modifiedEnergy_difference_integrable a μ hμ h
  have hf := (forceVelocity_integrable a μ hμ h).const_mul (σ-h/2)
  have hq := cellRemainder_integrable a μ hμ h σ
  rw [integral_add (f:=fun z=>modifiedEnergy U (gradient U) h z-phaseEnergy U z+
      (σ-h/2)*⟪gradient U z.1,flightVelocity (gradient U) h z⟫)
      (g:=cellRemainder U (gradient U) h σ) (hi.add hf) hq,
    integral_add hi hf,integral_const_mul] at hb
  linarith

theorem cell_endpoint_entropy_sum {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (μ : Measure (E×E)) [IsProbabilityMeasure μ] (hμ : MemLp id 2 μ)
    (hK : klDiv μ (phaseGibbs U)≠∞) (h : ℝ) :
    (klDiv (μ.map (cellState (gradient U) h 0)) (phaseGibbs U)).toReal+
      (klDiv (μ.map (cellState (gradient U) h h)) (phaseGibbs U)).toReal=
      2*(klDiv μ (phaseGibbs U)).toReal+
      2*(∫z,modifiedEnergy U (gradient U) h z-phaseEnergy U z ∂μ)+
      (∫z,cellRemainder U (gradient U) h h z ∂μ) := by
  have h0 := cell_entropy_split a μ hμ hK h 0
  have h1 := cell_entropy_split a μ hμ hK h h
  have hz : (∫z,cellRemainder U (gradient U) h 0 z ∂μ)=0 := by
    simp [cellRemainder]
  rw [hz] at h0
  linarith

theorem cellRemainder_mean_continuous {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (μ : Measure (E×E)) [IsProbabilityMeasure μ] (hμ : MemLp id 2 μ) (h : ℝ) :
    Continuous (fun σ : ℝ=>∫z,cellRemainder U (gradient U) h σ z ∂μ) := by
  let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
  let ν := μ.map (kickEquiv (gradient U) hg (h/2))
  have hm : MemLp id 2 ν :=
    (memLp_map_measure_iff measurable_id.aestronglyMeasurable
      (kickEquiv (gradient U) hg (h/2)).measurable.aemeasurable).mpr (a.kick_memLp hμ (h/2))
  have hc := continuous_freeFlight_potential a ν hm
  have he (σ : ℝ) : (∫z,cellRemainder U (gradient U) h σ z ∂μ)=
      (∫z,U (z.1+σ • z.2) ∂ν)-(∫z,U z.1 ∂μ)-
        σ*(∫z,⟪gradient U z.1,flightVelocity (gradient U) h z⟫ ∂μ) := by
    unfold cellRemainder
    have hi := a.potential_integrable (hμ.fst.add ((flightVelocity_memLp a μ hμ h).const_smul σ))
    have hu := a.potential_integrable hμ.fst
    have hf := (forceVelocity_integrable a μ hμ h).const_mul σ
    change Integrable (fun z=>U (z.1+σ • flightVelocity (gradient U) h z)) μ at hi
    change Integrable (fun z : E×E=>U z.1) μ at hu
    rw [integral_sub (f:=fun z=>U (z.1+σ • flightVelocity (gradient U) h z)-U z.1)
      (g:=fun z=>σ*⟪gradient U z.1,flightVelocity (gradient U) h z⟫) (hi.sub hu) hf,
      integral_sub hi hu,integral_const_mul]
    congr 2
    exact (integral_map (kickEquiv (gradient U) hg (h/2)).measurable.aemeasurable
      (show AEStronglyMeasurable (fun z : E×E=>U (z.1+σ • z.2)) ν from
        (a.twice_contDiff.continuous.measurable.comp
          (measurable_fst.add (measurable_const.smul measurable_snd))).aestronglyMeasurable)).symm
  simp_rw [he]
  exact (hc.sub continuous_const).sub (continuous_id.mul continuous_const)

theorem cell_weighted_entropy_identity {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (μ : Measure (E×E)) [IsProbabilityMeasure μ] (hμ : MemLp id 2 μ)
    (hK : klDiv μ (phaseGibbs U)≠∞) (A h : ℝ) :
    (∫σ in (0:ℝ)..h,(A-σ)*(klDiv (μ.map (cellState (gradient U) h σ)) (phaseGibbs U)).toReal)=
      (h*A-h^2/2)*((klDiv μ (phaseGibbs U)).toReal+
        (∫z,modifiedEnergy U (gradient U) h z-phaseEnergy U z ∂μ))-
      h^3/12*(∫z,⟪gradient U z.1,flightVelocity (gradient U) h z⟫ ∂μ)+
      (∫σ in (0:ℝ)..h,(A-σ)*(∫z,cellRemainder U (gradient U) h σ z ∂μ)) := by
  simp_rw [cell_entropy_split a μ hμ hK]
  exact weighted_affine_integral A h _ _ _ (cellRemainder_mean_continuous a μ hμ h)

theorem cell_potential_increment {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (μ : Measure (E×E)) [IsProbabilityMeasure μ] (hμ : MemLp id 2 μ) (h : ℝ) :
    (∫z,U z.1 ∂μ.map (cellState (gradient U) h h))-(∫z,U z.1 ∂μ)=
      h*(∫z,⟪gradient U z.1,flightVelocity (gradient U) h z⟫ ∂μ)+
      (∫z,cellRemainder U (gradient U) h h z ∂μ) := by
  let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
  rw [integral_map (show AEMeasurable (cellState (gradient U) h h) μ from
    (cellEquiv (gradient U) hg h h).measurable.aemeasurable)
    (show AEStronglyMeasurable (fun z : E×E=>U z.1) (μ.map (cellState (gradient U) h h)) from
      (a.twice_contDiff.continuous.measurable.comp measurable_fst).aestronglyMeasurable)]
  have hi := a.potential_integrable (hμ.fst.add ((flightVelocity_memLp a μ hμ h).const_smul h))
  have h0 := a.potential_integrable hμ.fst
  have hf := (forceVelocity_integrable a μ hμ h).const_mul h
  have he := integral_sub (μ:=μ)
    (f:=fun z : E×E=>U (z.1+h • flightVelocity (gradient U) h z)-U z.1)
    (g:=fun z : E×E=>h*⟪gradient U z.1,flightVelocity (gradient U) h z⟫)
    (hi.sub h0) hf
  rw [integral_sub (μ:=μ) (f:=fun z : E×E=>U (z.1+h • flightVelocity (gradient U) h z))
    (g:=fun z : E×E=>U z.1) hi h0,integral_const_mul] at he
  change (∫z,cellRemainder U (gradient U) h h z ∂μ)=
    (∫z,U (z.1+h • flightVelocity (gradient U) h z) ∂μ)-(∫z,U z.1 ∂μ)-
      h*(∫z,⟪gradient U z.1,flightVelocity (gradient U) h z⟫ ∂μ) at he
  change (∫z,U (z.1+h • flightVelocity (gradient U) h z) ∂μ)-(∫z,U z.1 ∂μ)=_
  linarith

end BreakingResonance
