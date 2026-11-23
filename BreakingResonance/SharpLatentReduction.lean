import BreakingResonance.SharpTransportLimit
import PersistencePays.CompactLatentReduction

noncomputable section
namespace BreakingResonance
open PersistencePays MeasureTheory ProbabilityTheory Set
universe u
variable {E:Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Exact reduction to a compact latent presentation. The displayed premise is
only the smooth analytic inequality; no probability or approximation facts
remain in it. -/
theorem sharp_gaussianSmoothedBound_of_compactBalls {U:E→ℝ} {m L:ℝ} (a:A1 U m L)
    (hcompact:∀(R:ℝ)(ν:ProbabilityMeasure (CompactLatentBall E R)),
      ∀ε:ℝ,0<ε→∀t:ℝ,0<t→
      a.corrector (transportJoint (fullGaussianOUKernel 1 ε ∘ₘ
        (compactLatentBallPushforward ν:Measure (E×E))) t)-
      a.corrector (fullGaussianOUKernel 1 ε ∘ₘ (compactLatentBallPushforward ν:Measure (E×E)))≤
      sharpFreeTransportRHS (fullGaussianOUKernel 1 ε ∘ₘ (compactLatentBallPushforward ν:Measure (E×E))) (positionGibbs U) t) :
    SharpGaussianSmoothedFreeTransportBound a := by
  intro ν hb ε hε t ht
  obtain ⟨R,hR⟩:=hb
  have hp:=compactLatentBallLaw_probability (ν:Measure (E×E)) hR
  let νc:ProbabilityMeasure (CompactLatentBall E R):=⟨compactLatentBallLaw (ν:Measure (E×E)) R,hp⟩
  have heq:compactLatentBallPushforward νc=ν:=by
    apply Subtype.ext
    exact compactLatentBallLaw_map _ hR
  have hh:=hcompact R νc ε hε t ht
  simp only [heq] at hh
  simpa only [additiveNoise_eq_fullGaussianOU] using hh
end BreakingResonance
