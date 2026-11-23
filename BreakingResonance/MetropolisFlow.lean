import BreakingResonance.VerletTrajectory
import PersistencePays.GaussianBridgeLaw

/-! Symmetry of the actual Metropolis stationary-flow expression. The
probability kernel and Gaussian disintegration are not encoded here. -/
namespace BreakingResonance
noncomputable section
open MeasureTheory PersistencePays
open scoped ENNReal

section General
variable {S X : Type*} [MeasurableSpace S] [MeasurableSpace X]

def acceptedWeight (p : S → ℝ≥0∞) (T : S → S) (z : S) : ℝ≥0∞ :=
  min (p z) (p (T z))

omit [MeasurableSpace S] in
theorem acceptedWeight_invariant (p : S → ℝ≥0∞) (T : S → S)
    (hT : Function.Involutive T) (z : S) :
    acceptedWeight p T (T z) = acceptedWeight p T z := by
  simp [acceptedWeight, hT z, min_comm]

theorem acceptedMeasure_invariant (μ : Measure S) (p : S → ℝ≥0∞)
    (hp : Measurable p) (T : S ≃ᵐ S) (hT : Function.Involutive T)
    (hmp : MeasurePreserving T μ μ) :
    (μ.withDensity (acceptedWeight p T)).map T =
      μ.withDensity (acceptedWeight p T) := by
  have hw : Measurable (acceptedWeight p T) := hp.min (hp.comp T.measurable)
  rw [map_density_equiv T μ _ hw, hmp.map_eq]
  congr 1
  funext z
  have hs : T.symm z = T z := by
    apply T.injective
    rw [T.apply_symm_apply, hT z]
  rw [hs]
  exact acceptedWeight_invariant p T hT z

def metropolisPositionFlow (μ : Measure S) (p : S → ℝ≥0∞)
    (T : S → S) (obs : S → X) : Measure (X × X) :=
  (μ.withDensity (acceptedWeight p T)).map (fun z => (obs z, obs (T z))) +
  (μ.withDensity (fun z => p z - acceptedWeight p T z)).map (fun z => (obs z, obs z))

theorem metropolisPositionFlow_symmetric (μ : Measure S) (p : S → ℝ≥0∞)
    (hp : Measurable p) (T : S ≃ᵐ S) (hT : Function.Involutive T)
    (hmp : MeasurePreserving T μ μ) (obs : S → X) (ho : Measurable obs) :
    (metropolisPositionFlow μ p T obs).map Prod.swap =
      metropolisPositionFlow μ p T obs := by
  let F : S → X × X := fun z => (obs z, obs (T z))
  have hF : Measurable F := ho.prodMk (ho.comp T.measurable)
  have hD : Measurable (fun z : S => (obs z, obs z)) := ho.prodMk ho
  have hcomp : Prod.swap ∘ F = F ∘ T := by
    funext z
    simp [F, hT z]
  have ha : ((μ.withDensity (acceptedWeight p T)).map F).map Prod.swap =
      (μ.withDensity (acceptedWeight p T)).map F := by
    rw [Measure.map_map measurable_swap hF, hcomp,
      ← Measure.map_map hF T.measurable, acceptedMeasure_invariant μ p hp T hT hmp]
  have hd : ((μ.withDensity (fun z => p z - acceptedWeight p T z)).map
      (fun z => (obs z, obs z))).map Prod.swap =
      (μ.withDensity (fun z => p z - acceptedWeight p T z)).map
      (fun z => (obs z, obs z)) := by
    rw [Measure.map_map measurable_swap hD]
    rfl
  unfold metropolisPositionFlow
  rw [Measure.map_add _ _ measurable_swap]
  exact congrArg₂ (· + ·) ha hd
end General

section Verlet
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def flippedTrajectoryEquiv (g : E → E) (hg : Measurable g) (h : ℝ) (n : ℕ) :
    (E × E) ≃ᵐ (E × E) where
  toFun := fun z => velocityFlip (trajectory g h z n)
  invFun := fun z => velocityFlip (trajectory g h z n)
  left_inv := flipped_trajectory_involutive g h n
  right_inv := flipped_trajectory_involutive g h n
  measurable_toFun := (flipped_trajectory_measurePreserving g hg h n).measurable
  measurable_invFun := (flipped_trajectory_measurePreserving g hg h n).measurable

theorem verlet_positionFlow_symmetric (g : E → E) (hg : Measurable g)
    (h : ℝ) (n : ℕ) (p : E × E → ℝ≥0∞) (hp : Measurable p) :
    (metropolisPositionFlow ((volume : Measure E).prod volume) p
      (flippedTrajectoryEquiv g hg h n) Prod.fst).map Prod.swap =
    metropolisPositionFlow ((volume : Measure E).prod volume) p
      (flippedTrajectoryEquiv g hg h n) Prod.fst :=
  metropolisPositionFlow_symmetric _ p hp (flippedTrajectoryEquiv g hg h n)
    (flipped_trajectory_involutive g h n)
    (flipped_trajectory_measurePreserving g hg h n) Prod.fst measurable_fst
end Verlet
end
end BreakingResonance
