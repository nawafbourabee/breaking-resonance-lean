import BreakingResonance.VerletTrajectory
import PersistencePays.KickEntropy
import PersistencePays.VolumeEntropy

/-! Finite entropy and exact entropy changes for the actual Verlet iterates
and the free-flight interpolation. -/
namespace BreakingResonance
noncomputable section
open PersistencePays MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def trajectoryEquiv (g : E → E) (hg : Measurable g) (h : ℝ) (n : ℕ) :
    (E×E) ≃ᵐ (E×E) where
  toFun z := trajectory g h z n
  invFun z := trajectory g (-h) z n
  left_inv := fun z=>trajectory_inverse g h z n
  right_inv := fun z=>by simpa only [neg_neg] using trajectory_inverse g (-h) z n
  measurable_toFun := (trajectory_measurePreserving g hg h n).measurable
  measurable_invFun := (trajectory_measurePreserving g hg (-h) n).measurable

theorem trajectory_memLp {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {p : ℝ≥0∞} {Z : Ω → E×E}
    {U : E → ℝ} {m L : ℝ} (a : A1 U m L) (hZ : MemLp Z p μ)
    (h : ℝ) (n : ℕ) : MemLp (fun ω=>trajectory (gradient U) h (Z ω) n) p μ := by
  induction n with
  | zero => simpa only [trajectory_zero] using hZ
  | succ n ih =>
    simp only [trajectory_succ]
    exact a.verlet_memLp ih h

theorem gibbs_volume_entropy_change {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (μ : Measure (E×E)) [IsProbabilityMeasure μ]
    (e : (E×E) ≃ᵐ (E×E))
    (he : MeasurePreserving e ((volume : Measure E).prod volume)
      ((volume : Measure E).prod volume))
    (hμ : MemLp id 2 μ) (heμ : MemLp e 2 μ)
    (hK : klDiv μ (phaseGibbs U)≠∞) :
    klDiv (μ.map e) (phaseGibbs U)≠∞ ∧
    (klDiv (μ.map e) (phaseGibbs U)).toReal=
      (klDiv μ (phaseGibbs U)).toReal+
        ∫z,phaseEnergy U (e z)-phaseEnergy U z ∂μ := by
  rw [phaseGibbs_eq_tilted U a.twice_contDiff.continuous.measurable a.gibbs_integrable] at hK ⊢
  exact volume_preserving_entropy_change _ (phaseEnergy U)
    (phaseEnergy_measurable U a.twice_contDiff.continuous.measurable)
    (phase_gibbs_integrable U a.gibbs_integrable) μ e he hK
    ((a.phaseEnergy_integrable heμ).sub (a.phaseEnergy_integrable hμ))

theorem trajectory_entropy_change {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (μ : Measure (E×E)) [IsProbabilityMeasure μ] (hμ : MemLp id 2 μ)
    (hK : klDiv μ (phaseGibbs U)≠∞) (h : ℝ) (n : ℕ) :
    klDiv (μ.map (fun z=>trajectory (gradient U) h z n)) (phaseGibbs U)≠∞ ∧
    (klDiv (μ.map (fun z=>trajectory (gradient U) h z n)) (phaseGibbs U)).toReal=
      (klDiv μ (phaseGibbs U)).toReal+
        ∫z,phaseEnergy U (trajectory (gradient U) h z n)-phaseEnergy U z ∂μ := by
  let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
  exact gibbs_volume_entropy_change a μ (trajectoryEquiv (gradient U) hg h n)
    (trajectory_measurePreserving (gradient U) hg h n) hμ
    (trajectory_memLp a hμ h n) hK

def cellState (g : E → E) (h σ : ℝ) (z : E×E) : E×E :=
  drift σ (kick g (h/2) z)

def cellEquiv (g : E → E) (hg : Measurable g) (h σ : ℝ) : (E×E) ≃ᵐ (E×E) :=
  (kickEquiv g hg (h/2)).trans (freeTransportEquiv σ)

theorem cellState_energy_identity (U : E → ℝ) (g : E → E) (h σ : ℝ) (z : E×E) :
    phaseEnergy U (cellState g h σ z)=
      modifiedEnergy U g h z+(σ-h/2)*⟪g z.1,flightVelocity g h z⟫+
      (U (z.1+σ • flightVelocity g h z)-U z.1-
        σ*⟪g z.1,flightVelocity g h z⟫) := by
  simp only [cellState,drift,kick,flightVelocity,modifiedEnergy,gradientCorrection,
    phaseEnergy_eq_norm,inner_sub_right,inner_smul_right,real_inner_self_eq_norm_sq,
    norm_sub_sq_real,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  rw [real_inner_comm (g z.1) z.2]
  ring

theorem cell_entropy_change {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (μ : Measure (E×E)) [IsProbabilityMeasure μ] (hμ : MemLp id 2 μ)
    (hK : klDiv μ (phaseGibbs U)≠∞) (h σ : ℝ) :
    klDiv (μ.map (cellState (gradient U) h σ)) (phaseGibbs U)≠∞ ∧
    (klDiv (μ.map (cellState (gradient U) h σ)) (phaseGibbs U)).toReal=
      (klDiv μ (phaseGibbs U)).toReal+
        ∫z,phaseEnergy U (cellState (gradient U) h σ z)-phaseEnergy U z ∂μ := by
  let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
  exact gibbs_volume_entropy_change a μ (cellEquiv (gradient U) hg h σ)
    ((drift_measurePreserving σ).comp (kick_measurePreserving (gradient U) hg (h/2)))
    hμ (drift_memLp (a.kick_memLp hμ (h/2)) σ) hK

end
end BreakingResonance
