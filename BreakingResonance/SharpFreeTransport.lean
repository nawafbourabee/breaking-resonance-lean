import BreakingResonance.SharpLatentReduction
import BreakingResonance.SharpCompactTransport

/-! Unconditional free-transport corrector inequality. The Gaussian smooth
case is proved from the actual law; truncation and entropy convergence then
remove the auxiliary smoothness and support conditions. -/
noncomputable section
namespace BreakingResonance
open PersistencePays MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal
universe u
variable {E:Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem sharp_gaussianSmoothedFreeTransportBound {U:E→ℝ} {m L:ℝ} (a:A1 U m L) :
    SharpGaussianSmoothedFreeTransportBound a := by
  apply (sharp_gaussianSmoothedBound_of_compactBalls a)
  intro R ν ε hε t ht
  exact (sharp_compactGaussian_freeTransport a) (ν:Measure (CompactLatentBall E R))
    Subtype.val continuous_subtype_val hε ht

/-- Sharp free-transport corrector bound for an arbitrary finite-entropy joint law. -/
theorem sharp_free_transport_corrector {U:E→ℝ} {m L:ℝ} (a:A1 U m L)
    (μ:ProbabilityMeasure (E×E)) (hμ:MemLp id 2 (μ:Measure (E×E)))
    (hK:klDiv (μ:Measure (E×E)) (phaseGibbs U)≠∞) {t:ℝ} (ht:0<t) :
    a.corrector (transportJoint (μ:Measure (E×E)) t)-a.corrector (μ:Measure (E×E))≤
      sharpFreeTransportRHS (μ:Measure (E×E)) (positionGibbs U) t :=
  (sharp_free_transport_of_smoothed_bound a) (sharp_gaussianSmoothedFreeTransportBound a) μ hμ hK ht
end BreakingResonance
