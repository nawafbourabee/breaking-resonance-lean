import BreakingResonance.StepSizeParameters
import BreakingResonance.RoundedFourierBounds

noncomputable section

namespace BreakingResonance

def upperDurationCutoff (m bρ δρ : ℝ) : ℝ :=
  4*bρ/(δρ*Real.sqrt m)

def upperFourierConstant (bρ δρ : ℝ) : ℝ :=
  let k := evenHarmonic (4*bρ/δρ+1)
  let ζ := δρ/(4*(k:ℝ)^2)
  min (δρ/64) (min ζ (1-Real.cos (ζ/2)))/8

def upperSpectralConstant (bρ δρ : ℝ) : ℝ :=
  let kρ := evenHarmonic (2*(bρ+1))
  let ζρ := δρ/(2*(kρ:ℝ)^2)
  1-Real.cos (ζρ/2)

def upperHorizonFactor (bρ δρ : ℝ) : ℝ :=
  4*(bρ+δρ)/δρ

def upperC₁ (bρ δρ : ℝ) : ℝ :=
  let η := upperFourierConstant bρ δρ/600
  upperStepConstant δρ η (upperHorizonFactor bρ δρ) (2*Real.log (64/η))

/-- A uniform value of c₂ obtained by using the lower bound for the
retained duration probability. -/
def upperC₂ (bρ δρ : ℝ) : ℝ :=
  let φ := (1-δρ/4)*upperFourierConstant bρ δρ/60
  6/(upperSpectralConstant bρ δρ*φ^2)

theorem upperConstants_fourier_pos {bρ δρ : ℝ} (hb : 0 < bρ) (hδ : 0 < δρ) (hδ₁ : δρ ≤ 1) :
    (0 < upperFourierConstant bρ δρ ∧ upperFourierConstant bρ δρ ≤ 1) ∧
    (0 < upperSpectralConstant bρ δρ ∧ upperSpectralConstant bρ δρ ≤ 1) := by
  dsimp only [upperFourierConstant,upperSpectralConstant]
  obtain ⟨hζ,hζ₁⟩ := evenHarmonic_divisor_bounds
    (show 0 < 4*bρ/δρ+1 by positivity) hδ hδ₁ (by norm_num : (1:ℝ) ≤ 4)
  obtain ⟨hζρ,hζρ₁⟩ := evenHarmonic_divisor_bounds
    (show 0 < 2*(bρ+1) by positivity) hδ hδ₁ (by norm_num : (1:ℝ) ≤ 2)
  have hm := lt_min (show 0 < δρ/64 by positivity)
    (lt_min hζ (bernoulli_gap_bounds hζ hζ₁).1)
  refine ⟨⟨div_pos hm (by norm_num),?_⟩,?_⟩
  · let ζ := δρ/(4*(evenHarmonic (4*bρ/δρ+1):ℝ)^2)
    have h := min_le_left (δρ/64) (min ζ (1-Real.cos (ζ/2)))
    exact (div_le_div_of_nonneg_right h (by norm_num : (0:ℝ) ≤ 8)).trans
      (by linarith only [hδ₁])
  · exact ⟨(bernoulli_gap_bounds hζρ hζρ₁).1,(bernoulli_gap_bounds hζρ hζρ₁).2.trans hζρ₁⟩

theorem cutoff_rescaled {m bρ δρ : ℝ} (hm : 0 < m) (hδ : 0 < δρ) :
    Real.sqrt m*upperDurationCutoff m bρ δρ = 4*bρ/δρ := by
  unfold upperDurationCutoff
  field_simp [(Real.sqrt_pos.mpr hm).ne',hδ.ne']

theorem horizon_rescaled {m bρ δρ : ℝ} (hm : 0 < m) (hδ : 0 < δρ) :
    upperDurationCutoff m bρ δρ+4/Real.sqrt m = upperHorizonFactor bρ δρ/Real.sqrt m := by
  unfold upperDurationCutoff upperHorizonFactor
  field_simp [(Real.sqrt_pos.mpr hm).ne',hδ.ne']

theorem upperConstants_pos {bρ δρ : ℝ} (hb : 0 < bρ) (hδ : 0 < δρ) (hδ₁ : δρ ≤ 1) :
    0 < upperC₁ bρ δρ ∧ 0 < upperC₂ bρ δρ := by
  obtain ⟨hc,hβ⟩ := upperConstants_fourier_pos hb hδ hδ₁
  constructor
  · unfold upperC₁ upperStepConstant
    exact (div_pos (by norm_num) (Real.sqrt_pos.mpr hδ)).trans_le (le_max_left _ _)
  · dsimp only [upperC₂]
    have hp : 0 < 1-δρ/4 := by linarith only [hδ₁]
    have hf : 0 < (1-δρ/4)*upperFourierConstant bρ δρ/60 := div_pos (mul_pos hp hc.1) (by norm_num)
    have hb := hβ.1
    positivity

end BreakingResonance

#print axioms BreakingResonance.upperConstants_pos
