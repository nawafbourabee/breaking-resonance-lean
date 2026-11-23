import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.RealImaginaryPart
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-! Order bounds for continuous functional calculus of the real part of a
unitary operator. The scalar multiplier is the cosine series in Lemma 5.2. -/
noncomputable section
namespace BreakingResonance
open ComplexStarModule

def cosineSeries (w : ℕ → ℝ) (θ : ℝ) : ℝ :=
  ∑' j : ℕ, w j * Real.cos (j * θ)

theorem continuous_cosineSeries {w : ℕ → ℝ} (hw : ∀ j, 0 ≤ w j)
    (hsum : Summable w) : Continuous (cosineSeries w) := by
  unfold cosineSeries
  apply continuous_tsum (fun _ => by fun_prop) hsum
  intro n θ
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw n)]
  exact mul_le_of_le_one_right (hw n) (abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩)

theorem cos_mul_arccos_eq_re_pow {z : ℂ} (hz : ‖z‖ = 1) (j : ℕ) :
    Real.cos (j * Real.arccos z.re) = (z^j).re := by
  have hz₀ : z ≠ 0 := by
    intro he
    simp [he] at hz
  have he : Complex.exp (z.arg * Complex.I) = z := by
    simpa only [hz, Complex.ofReal_one, one_mul] using Complex.norm_mul_exp_arg_mul_I z
  have hpow : z^j = Complex.exp (((j : ℝ)*z.arg) * Complex.I) := by
    calc
      _ = (Complex.exp (z.arg * Complex.I))^j := congrArg (· ^ j) he.symm
      _ = _ := by rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have hcos : (z^j).re = Real.cos (j*z.arg) := by
    rw [hpow]
    simpa only [Complex.ofReal_mul, Complex.ofReal_natCast] using
      Complex.exp_ofReal_mul_I_re ((j : ℝ) * z.arg)
  rw [hcos]
  by_cases hIm : 0 ≤ z.im
  · have ha := Complex.arg_of_im_nonneg_of_ne_zero hIm hz₀
    rw [hz, div_one] at ha
    rw [ha]
  · have ha := Complex.arg_of_im_neg (lt_of_not_ge hIm)
    rw [hz, div_one] at ha
    rw [ha, mul_neg, Real.cos_neg]

section FunctionalCalculus

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- Apply the Fourier lower bound to a selfadjoint operator with spectrum in
the interval [-1,1]. For the real part of a unitary, the angle is arccos x. -/
theorem cfc_cosineSeries_lower
    {w : ℕ → ℝ} (hw : ∀ j, 0 ≤ w j) (hsum : Summable w)
    (B : A) (hB : IsSelfAdjoint B) (β : ℝ)
    (hβ : ∀ θ ∈ Set.Icc (-Real.pi) Real.pi, -1 + β ≤ cosineSeries w θ) :
    algebraMap ℝ A (-1 + β) ≤ cfc (fun x => cosineSeries w (Real.arccos x)) B := by
  have hc := (continuous_cosineSeries hw hsum).comp Real.continuous_arccos
  apply (algebraMap_le_cfc_iff _ _ B hc.continuousOn hB).2
  intro x _
  exact hβ (Real.arccos x)
    ⟨(neg_nonpos.mpr Real.pi_pos.le).trans (Real.arccos_nonneg _), Real.arccos_le_pi _⟩

theorem cfc_cosineSeries_comparison
    {w q : ℕ → ℝ} (hw : ∀ j, 0 ≤ w j) (hq : ∀ j, 0 ≤ q j)
    (hwSum : Summable w) (hqSum : Summable q) (B : A) (hB : IsSelfAdjoint B)
    (c : ℝ)
    (hgap : ∀ θ ∈ Set.Icc (-Real.pi) Real.pi,
      c * (1 - cosineSeries q θ) ≤ 1 - cosineSeries w θ) :
    cfc (fun x => c * (1 - cosineSeries q (Real.arccos x))) B ≤
      cfc (fun x => 1 - cosineSeries w (Real.arccos x)) B := by
  have hwc := (continuous_cosineSeries hw hwSum).comp Real.continuous_arccos
  have hqc := (continuous_cosineSeries hq hqSum).comp Real.continuous_arccos
  apply (cfc_le_iff _ _ B (continuous_const.mul (continuous_const.sub hqc)).continuousOn
    (continuous_const.sub hwc).continuousOn hB).2
  intro x _
  exact hgap (Real.arccos x)
    ⟨(neg_nonpos.mpr Real.pi_pos.le).trans (Real.arccos_nonneg _), Real.arccos_le_pi _⟩

omit [PartialOrder A] [StarOrderedRing A] in
/-- The operator defined by the cosine multiplier is the norm-convergent
mixture of the symmetric powers of a unitary. -/
theorem cfc_cosineSeries_unitary
    {w : ℕ → ℝ} (hw : ∀ j, 0 ≤ w j) (hsum : Summable w) (U : unitary A) :
    cfc (fun x => cosineSeries w (Real.arccos x)) (↑(ℜ (U : A)) : A) =
      ∑' j : ℕ, (w j : ℂ) • (↑(ℜ ((U : A)^j)) : A) := by
  let a : A := U
  have hn : IsStarNormal a := isStarNormal_of_mem_unitary U.property
  have hz (z : spectrum ℂ a) : ‖(z : ℂ)‖ = 1 :=
    spectrum.norm_eq_one_of_unitary U.property z.property
  let F (j : ℕ) : C(spectrum ℂ a, ℂ) :=
    ⟨fun z => (w j * ((z : ℂ)^j).re : ℝ), by fun_prop⟩
  have hF (j : ℕ) : ‖F j‖ ≤ w j := by
    apply (ContinuousMap.norm_le _ (hw j)).2
    intro z
    change ‖((w j * ((z : ℂ)^j).re : ℝ) : ℂ)‖ ≤ w j
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw j)]
    apply mul_le_of_le_one_right (hw j)
    exact (Complex.abs_re_le_norm _).trans (by rw [norm_pow, hz, one_pow])
  have hs : Summable F := hsum.of_norm_bounded hF
  have hcos : Continuous (fun x => cosineSeries w (Real.arccos x)) :=
    (continuous_cosineSeries hw hsum).comp Real.continuous_arccos
  let f : ℂ → ℂ := fun z => (cosineSeries w (Real.arccos z.re) : ℝ)
  have hf : Continuous f :=
    Complex.continuous_ofReal.comp (hcos.comp Complex.continuous_re)
  have hFsum : (∑' j, F j) = ⟨fun z : spectrum ℂ a => f z, hf.comp continuous_subtype_val⟩ := by
    ext z
    change (ContinuousMap.evalCLM ℂ z) (∑' j, F j) = _
    rw [ContinuousLinearMap.map_tsum _ hs]
    change (∑' j : ℕ, ((w j * ((z : ℂ)^j).re : ℝ) : ℂ)) = f z
    unfold f cosineSeries
    simp_rw [← cos_mul_arccos_eq_re_pow (hz z)]
    symm
    apply Complex.ofRealCLM.map_tsum
    apply hsum.of_norm_bounded (fun j => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw j)]
    exact mul_le_of_le_one_right (hw j) (abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩)
  have hsingle (j : ℕ) : cfcHom hn (F j) = (w j : ℂ) • (↑(ℜ (a^j)) : A) := by
    let g : ℂ → ℂ := fun z => ((w j * (z^j).re : ℝ) : ℂ)
    have hm : Continuous g := by dsimp only [g]; fun_prop
    have hc := cfc_apply g a hn hm.continuousOn
    change cfc g a = cfcHom hn (F j) at hc
    rw [← hc]
    change cfc (fun z : ℂ => ((w j * (z^j).re : ℝ) : ℂ)) a = _
    simp only [Complex.ofReal_mul]
    change cfc (fun z : ℂ => (w j : ℂ) • ((z^j).re : ℂ)) a = _
    have hcont₁ : Continuous (fun z : ℂ => ((z^j).re : ℂ)) := by fun_prop
    rw [cfc_smul _ _ _ hcont₁.continuousOn]
    have hcont₂ : Continuous (fun z : ℂ => (z.re : ℂ)) := by fun_prop
    have hn_pow : IsStarNormal (a^j) := isStarNormal_of_mem_unitary (pow_mem U.property j)
    rw [cfc_comp_pow (fun z : ℂ => (z.re : ℂ)) j a hcont₂.continuousOn hn,
      cfc_re_id (a^j) hn_pow]
  change cfc (fun x => cosineSeries w (Real.arccos x)) (↑(ℜ a) : A) = _
  rw [← cfc_comp_re _ a hcos.continuousOn hn]
  change cfc f a = _
  rw [cfc_apply _ a hn hf.continuousOn]
  change cfcHom hn ⟨fun z : spectrum ℂ a => f z, hf.comp continuous_subtype_val⟩ = _
  rw [← hFsum]
  have hcont := (isometry_cfcHom (R := ℂ) a hn).continuous
  have ht := hs.hasSum.map (cfcHom hn).toAddMonoidHom hcont
  exact ht.tsum_eq.symm.trans (tsum_congr hsingle)

/-- The symmetrized power average has the lower spectral bound supplied by
the cosine series. -/
theorem unitary_cosineSeries_lower {w : ℕ → ℝ} (hw : ∀ j, 0 ≤ w j)
    (hsum : Summable w) (U : unitary A) (β : ℝ)
    (hβ : ∀ θ ∈ Set.Icc (-Real.pi) Real.pi, -1 + β ≤ cosineSeries w θ) :
    algebraMap ℝ A (-1 + β) ≤ ∑' j : ℕ, (w j : ℂ) • (↑(ℜ ((U : A)^j)) : A) := by
  rw [← cfc_cosineSeries_unitary hw hsum U]
  exact cfc_cosineSeries_lower hw hsum (↑(ℜ (U : A)) : A) (ℜ (U : A)).property β hβ

theorem unitary_cosineSeries_comparison {w q : ℕ → ℝ}
    (hw : ∀ j, 0 ≤ w j) (hq : ∀ j, 0 ≤ q j)
    (hwSum : Summable w) (hqSum : Summable q) (U : unitary A) (c : ℝ)
    (hgap : ∀ θ ∈ Set.Icc (-Real.pi) Real.pi,
      c * (1 - cosineSeries q θ) ≤ 1 - cosineSeries w θ) :
    c • (1 - ∑' j : ℕ, (q j : ℂ) • (↑(ℜ ((U : A)^j)) : A)) ≤
      1 - ∑' j : ℕ, (w j : ℂ) • (↑(ℜ ((U : A)^j)) : A) := by
  let B : A := ↑(ℜ (U : A))
  have hB : IsSelfAdjoint B := (ℜ (U : A)).property
  have hwc : Continuous (fun x => cosineSeries w (Real.arccos x)) :=
    (continuous_cosineSeries hw hwSum).comp Real.continuous_arccos
  have hqc : Continuous (fun x => cosineSeries q (Real.arccos x)) :=
    (continuous_cosineSeries hq hqSum).comp Real.continuous_arccos
  have h := cfc_cosineSeries_comparison hw hq hwSum hqSum B hB c hgap
  have hOne : cfc (fun _ : ℝ => (1 : ℝ)) B = 1 := by
    change cfc (1 : ℝ → ℝ) B = 1
    exact cfc_one ℝ B hB
  have hq' : cfc (fun x => c * (1 - cosineSeries q (Real.arccos x))) B =
      c • (1 - cfc (fun x => cosineSeries q (Real.arccos x)) B) := by
    change cfc (fun x => c • (1 - cosineSeries q (Real.arccos x))) B = _
    rw [cfc_smul c (fun x => 1 - cosineSeries q (Real.arccos x)) B
      (continuous_const.sub hqc).continuousOn,
      cfc_sub (fun _ : ℝ => 1) _ B continuous_const.continuousOn hqc.continuousOn, hOne]
  have hw' : cfc (fun x => 1 - cosineSeries w (Real.arccos x)) B =
      1 - cfc (fun x => cosineSeries w (Real.arccos x)) B := by
    rw [cfc_sub (fun _ : ℝ => 1) _ B continuous_const.continuousOn hwc.continuousOn, hOne]
  rw [hq', hw'] at h
  rw [← cfc_cosineSeries_unitary hq hqSum U, ← cfc_cosineSeries_unitary hw hwSum U]
  exact h

end FunctionalCalculus
end BreakingResonance

#print axioms BreakingResonance.continuous_cosineSeries
#print axioms BreakingResonance.cfc_cosineSeries_lower
#print axioms BreakingResonance.cfc_cosineSeries_comparison

#print axioms BreakingResonance.cfc_cosineSeries_unitary
