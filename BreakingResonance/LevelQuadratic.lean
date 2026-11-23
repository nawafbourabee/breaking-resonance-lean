import BreakingResonance.DensityLevels
import BreakingResonance.FourierOperators
import BreakingResonance.VerletComposition
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! The Fourier quadratic forms on the density levels in Lemma 5.2. -/
noncomputable section
namespace BreakingResonance
open MeasureTheory Set ComplexStarModule
open scoped ENNReal InnerProductSpace

variable {S : Type*} [MeasurableSpace S]

/-- The test function restricted to the part of phase space above a given density level. -/
def densityTest (p : S → ℝ≥0∞) (f : S → ℝ) (u : ℝ) (z : S) : ℝ :=
  (Ioc 0 (p z).toReal).indicator (fun _ => f z) u

omit [MeasurableSpace S] in
theorem densityTest_eq_indicator (p : S → ℝ≥0∞) (f : S → ℝ) {u : ℝ} (hu : 0 < u) :
    densityTest p f u = ({z | u ≤ (p z).toReal}).indicator f := by
  funext z
  by_cases hz : u ≤ (p z).toReal
  · simp [densityTest, hu, hz]
  · simp [densityTest, hz]

omit [MeasurableSpace S] in
theorem densityTest_eq_zero (p : S → ℝ≥0∞) (f : S → ℝ) {u : ℝ} (hu : u ≤ 0) :
    densityTest p f u = 0 := by
  funext z
  simp [densityTest, not_lt.mpr hu]

theorem densityTest_memLp (μ : Measure S) (p : S → ℝ≥0∞)
    (hp : ∀ z, p z ≠ ∞) (hpm : Measurable p) (f : S → ℝ) (hfm : Measurable f)
    (hf : MemLp f 2 (μ.withDensity p)) (u : ℝ) :
    MemLp (densityTest p f u) 2 μ := by
  by_cases hu : 0 < u
  · rw [densityTest_eq_indicator p f hu]
    exact densityLevel_memLp μ p hp hpm f hfm hf hu
  · rw [densityTest_eq_zero p f (le_of_not_gt hu)]
    exact MemLp.zero

section Pairing

variable (μ : Measure S) (F : S ≃ᵐ S) (hF : MeasurePreserving F μ μ)
variable (g : S → ℝ) (hg : MemLp g 2 μ)

local notation "𝓗" => Lp ℂ 2 μ
local notation "𝓐" => (𝓗 →L[ℂ] 𝓗)

def reQuadraticCLM (x : 𝓗) : 𝓐 →L[ℝ] ℝ :=
  (RCLike.reCLM (K := ℂ)).comp
    (((innerSL ℂ x).comp (ContinuousLinearMap.apply ℂ 𝓗 x)).restrictScalars ℝ)

theorem reQuadraticCLM_one (x : 𝓗) : reQuadraticCLM μ x 1 = ‖x‖^2 := by
  exact (norm_sq_eq_re_inner (𝕜 := ℂ) x).symm

theorem reQuadraticCLM_mono (x : 𝓗) : Monotone (reQuadraticCLM μ x) := by
  intro A B h
  have hpos : (B - A).IsPositive :=
    ContinuousLinearMap.nonneg_iff_isPositive.mp (sub_nonneg.mpr h)
  have hp := hpos.re_inner_nonneg_right x
  change 0 ≤ reQuadraticCLM μ x (B - A) at hp
  rwa [map_sub, sub_nonneg] at hp

/-- The representative of a real square-integrable function in complex L². -/
def realTestLp : 𝓗 := (Complex.ofRealCLM.comp_memLp' hg).toLp _

theorem realTestLp_ae : (realTestLp μ g hg : S → ℂ) =ᵐ[μ] fun z => (g z : ℂ) :=
  MemLp.coeFn_toLp _

theorem lpComposition_re_inner (j : ℕ) :
    (⟪realTestLp μ g hg,
      (((lpCompositionUnitary μ F hF : 𝓐)^j) (realTestLp μ g hg))⟫_ℂ).re =
      ∫ z, g z * g ((F : S → S)^[j] z) ∂μ := by
  let x := realTestLp μ g hg
  let U := lpCompositionUnitary μ F hF
  have he : (x : S → ℂ) =ᵐ[μ] fun z => (g z : ℂ) := realTestLp_ae μ g hg
  have hiter : MeasurePreserving ((F : S → S)^[j]) μ μ := hF.iterate j
  have hpow : (((U : 𝓐)^j) x : S → ℂ) =ᵐ[μ] fun z => (g ((F : S → S)^[j] z) : ℂ) := by
    rw [← SubmonoidClass.coe_pow]
    exact (lpCompositionUnitary_pow_apply_ae μ F hF j x).trans
      (hiter.quasiMeasurePreserving.ae_eq_comp he)
  change (⟪x, ((U : 𝓐)^j) x⟫_ℂ).re = _
  rw [L2.inner_def]
  have hi : Integrable (fun z => ⟪x z, (((U : 𝓐)^j) x) z⟫_ℂ) μ := L2.integrable_inner _ _
  change RCLike.re (∫ z, ⟪x z, (((U : 𝓐)^j) x) z⟫_ℂ ∂μ) = _
  rw [← integral_re hi]
  apply integral_congr_ae
  filter_upwards [he, hpow] with z hx hy
  rw [hx, hy, RCLike.inner_apply]
  simp [mul_comm]

theorem re_inner_realPart (A : 𝓐) (x : 𝓗) :
    (⟪x, (↑(ℜ A) : 𝓐) x⟫_ℂ).re = (⟪x, A x⟫_ℂ).re := by
  rw [realPart_apply_coe, ContinuousLinearMap.star_eq_adjoint]
  change (⟪x, (2 : ℝ)⁻¹ • (A x + A.adjoint x)⟫_ℂ).re = _
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_right, inner_add_right,
    ContinuousLinearMap.adjoint_inner_right]
  change ((↑((2 : ℝ)⁻¹) : ℂ) * (⟪x, A x⟫_ℂ + ⟪A x, x⟫_ℂ)).re = _
  rw [Complex.re_ofReal_mul, Complex.add_re]
  have he : (⟪A x, x⟫_ℂ).re = (⟪x, A x⟫_ℂ).re :=
    inner_re_symm (𝕜 := ℂ) (A x) x
  rw [he]
  ring

theorem lpComposition_inner_abs_le (j : ℕ) (x : 𝓗) :
    |(⟪x, (((lpCompositionUnitary μ F hF : 𝓐)^j) x)⟫_ℂ).re| ≤ ‖x‖^2 := by
  let U := lpCompositionUnitary μ F hF
  have hnorm : ‖((U : 𝓐)^j) x‖ = ‖x‖ := by
    rw [← SubmonoidClass.coe_pow]
    exact (Unitary.linearIsometryEquiv (U^j)).norm_map x
  calc
    _ ≤ ‖⟪x, ((U : 𝓐)^j) x⟫_ℂ‖ := Complex.abs_re_le_norm _
    _ ≤ ‖x‖ * ‖((U : 𝓐)^j) x‖ := norm_inner_le_norm x _
    _ = ‖x‖^2 := by rw [hnorm, pow_two]

theorem lpComposition_norm_sq :
    ‖realTestLp μ g hg‖^2 = ∫ z, g z ^ 2 ∂μ := by
  let x := realTestLp μ g hg
  rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
  change RCLike.re ⟪x, x⟫_ℂ = _
  rw [L2.inner_def, ← integral_re (L2.integrable_inner x x)]
  apply integral_congr_ae
  filter_upwards [realTestLp_ae μ g hg] with z hz
  change RCLike.re ⟪x z, x z⟫_ℂ = g z ^ 2
  rw [hz, RCLike.inner_apply]
  simp [pow_two]

end Pairing

section DensityLevels

variable (μ : Measure S) [SFinite μ] (p : S → ℝ≥0∞) (hp : ∀ z, p z ≠ ∞)
variable (hpm : Measurable p) (f : S → ℝ) (hfm : Measurable f)
variable (hf : MemLp f 2 (μ.withDensity p))
variable (F : S ≃ᵐ S) (hF : MeasurePreserving F μ μ)

local notation "𝓗" => Lp ℂ 2 μ
local notation "𝓐" => (𝓗 →L[ℂ] 𝓗)
local notation "g" => (fun u => realTestLp μ (densityTest p f u)
  (densityTest_memLp μ p hp hpm f hfm hf u))
local notation "U" => lpCompositionUnitary μ F hF

def levelCross (μ : Measure S) (p : S → ℝ≥0∞) (f : S → ℝ)
    (F : S → S) (j : ℕ) (u : ℝ) : ℝ :=
  ∫ z, densityTest p f u z * densityTest p f u (F^[j] z) ∂μ

include hp hpm hfm hf hF in
theorem levelCross_integrable (j : ℕ) : Integrable (levelCross μ p f F j) := by
  let T := (F : S → S)^[j]
  have ht : MeasurePreserving T μ μ := hF.iterate j
  have hi := acceptedWeight_integrable_product μ p hp hpm T ht f hfm hf
  have h := (integrable_integral_acceptedWeight_levels μ p hp hpm T ht.measurable
    (fun z => f z * f (T z)) (hfm.mul (hfm.comp ht.measurable)) hi).1
  have he (u : ℝ) (z : S) :
      (Ioc 0 (p z).toReal).indicator (1 : ℝ → ℝ) u *
        (Ioc 0 (p (T z)).toReal).indicator (1 : ℝ → ℝ) u * (f z * f (T z)) =
        densityTest p f u z * densityTest p f u (T z) := by
    by_cases hz : u ∈ Ioc 0 (p z).toReal <;> by_cases hT : u ∈ Ioc 0 (p (T z)).toReal <;>
      simp [densityTest, indicator, hz, hT]
  simp_rw [he] at h
  exact h

omit [SFinite μ] in
theorem levelCross_eq_inner (j : ℕ) (u : ℝ) :
    levelCross μ p f F j u = (⟪g u, (↑(ℜ ((U : 𝓐)^j)) : 𝓐) (g u)⟫_ℂ).re := by
  rw [re_inner_realPart, lpComposition_re_inner]
  rfl

theorem levelNorm_integral :
    Integrable (fun u : ℝ => ‖g u‖^2) ∧
      (∫ u : ℝ, ‖g u‖^2) = ∫ z, f z ^ 2 ∂μ.withDensity p := by
  simp_rw [lpComposition_norm_sq]
  exact integrable_integral_densityLevel_sq μ p hp hpm f hfm hf

omit [SFinite μ] in
include hF in
theorem levelCross_abs_le (j : ℕ) (u : ℝ) :
    |levelCross μ p f F j u| ≤ ‖g u‖^2 := by
  rw [levelCross_eq_inner μ p hp hpm f hfm hf F hF, re_inner_realPart]
  exact lpComposition_inner_abs_le μ F hF _ _

def cosineOperator (w : ℕ → ℝ) : 𝓐 :=
  ∑' j : ℕ, (w j : ℂ) • (↑(ℜ ((U : 𝓐)^j)) : 𝓐)

omit [SFinite μ] in
theorem summable_cosineOperator_terms {w : ℕ → ℝ} (hw : ∀ j, 0 ≤ w j)
    (hs : Summable w) : Summable
      (fun j : ℕ => (w j : ℂ) • (↑(ℜ ((U : 𝓐)^j)) : 𝓐)) := by
  apply hs.of_norm_bounded
  intro j
  have hn : ‖(U : 𝓐)^j‖ ≤ 1 := by
    have hmul := CStarRing.norm_coe_unitary_mul (U^j) (1 : 𝓐)
    rw [mul_one, SubmonoidClass.coe_pow] at hmul
    have hone : ‖(1 : 𝓐)‖ ≤ 1 := by
      apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      intro x
      simp
    exact hmul.le.trans hone
  rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (hw j)]
  exact mul_le_of_le_one_right (hw j) ((realPart.norm_le _).trans hn)

omit [SFinite μ] in
theorem levelCross_weighted (w : ℕ → ℝ) (hw : ∀ j, 0 ≤ w j)
    (hs : Summable w) (u : ℝ) :
    (∑' j, w j * levelCross μ p f F j u) =
      (⟪g u, cosineOperator μ F hF w (g u)⟫_ℂ).re := by
  let x : 𝓗 := g u
  let Q := reQuadraticCLM μ x
  change _ = Q (cosineOperator μ F hF w)
  rw [cosineOperator, Q.map_tsum (summable_cosineOperator_terms μ F hF hw hs)]
  apply tsum_congr
  intro j
  rw [levelCross_eq_inner μ p hp hpm f hfm hf F hF]
  change _ = (⟪x, ((w j : ℂ) • (↑(ℜ ((U : 𝓐)^j)) : 𝓐)) x⟫_ℂ).re
  rw [smul_apply, inner_smul_right]
  simp [x]

include hp hpm hfm hf hF in
theorem summable_levelCross_integral_norm (w : ℕ → ℝ) (hw : ∀ j, 0 ≤ w j)
    (hs : Summable w) :
    Summable fun j => ∫ u : ℝ, ‖w j * levelCross μ p f F j u‖ := by
  apply (hs.mul_right (∫ u : ℝ, ‖g u‖^2)).of_norm_bounded
  intro j
  rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _), ← integral_const_mul]
  have hj := (levelCross_integrable μ p hp hpm f hfm hf F hF j).const_mul (w j)
  refine integral_mono hj.norm
    ((levelNorm_integral μ p hp hpm f hfm hf).1.const_mul (w j)) ?_
  intro u
  change ‖w j * levelCross μ p f F j u‖ ≤ w j * ‖g u‖^2
  rw [norm_mul, Real.norm_of_nonneg (hw j), Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (levelCross_abs_le μ p hp hpm f hfm hf F hF j u) (hw j)

def integratedCosineForm (w : ℕ → ℝ) : ℝ :=
  ∫ u : ℝ, reQuadraticCLM μ (g u) (cosineOperator μ F hF w)

theorem integratedCosineForm_eq_tsum (w : ℕ → ℝ) (hw : ∀ j, 0 ≤ w j)
    (hs : Summable w) :
    integratedCosineForm μ p hp hpm f hfm hf F hF w =
      ∑' j, w j * ∫ u : ℝ, levelCross μ p f F j u := by
  have hj (j : ℕ) := (levelCross_integrable μ p hp hpm f hfm hf F hF j).const_mul (w j)
  rw [integratedCosineForm]
  have hu (u : ℝ) : reQuadraticCLM μ (g u) (cosineOperator μ F hF w) = _ :=
    (levelCross_weighted μ p hp hpm f hfm hf F hF w hw hs u).symm
  simp_rw [hu, ← integral_const_mul]
  exact (integral_tsum_of_summable_integral_norm hj
    (summable_levelCross_integral_norm μ p hp hpm f hfm hf F hF w hw hs)).symm

theorem integratedCosineForm_integrable (w : ℕ → ℝ) (hw : ∀ j, 0 ≤ w j)
    (hs : Summable w) :
    Integrable (fun u : ℝ => reQuadraticCLM μ (g u) (cosineOperator μ F hF w)) := by
  have hj (j : ℕ) := (levelCross_integrable μ p hp hpm f hfm hf F hF j).const_mul (w j)
  have hu (u : ℝ) : reQuadraticCLM μ (g u) (cosineOperator μ F hF w) = _ :=
    (levelCross_weighted μ p hp hpm f hfm hf F hF w hw hs u).symm
  simp_rw [hu]
  have hm : AEMeasurable (fun u : ℝ => ∑' j, w j * levelCross μ p f F j u) volume :=
    AEMeasurable.tsum (fun j => (hj j).aestronglyMeasurable.aemeasurable)
  apply ((levelNorm_integral μ p hp hpm f hfm hf).1.const_mul (∑' j, w j)).mono'
    hm.aestronglyMeasurable
  filter_upwards with u
  have hle (j : ℕ) : ‖w j * levelCross μ p f F j u‖ ≤ w j * ‖g u‖^2 := by
    rw [norm_mul, Real.norm_of_nonneg (hw j), Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (levelCross_abs_le μ p hp hpm f hfm hf F hF j u) (hw j)
  have hsum := hs.mul_right (‖g u‖^2)
  have hnorm : Summable fun j => ‖w j * levelCross μ p f F j u‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle hsum
  calc
    _ ≤ ∑' j, ‖w j * levelCross μ p f F j u‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' j, w j * ‖g u‖^2 := hnorm.tsum_le_tsum hle hsum
    _ = _ := tsum_mul_right

theorem integratedCosineForm_lower (w : ℕ → ℝ) (hw : ∀ j, 0 ≤ w j)
    (hs : Summable w) (β : ℝ)
    (hβ : ∀ θ ∈ Icc (-Real.pi) Real.pi, -1 + β ≤ cosineSeries w θ) :
    (-1 + β) * (∫ z, f z ^ 2 ∂μ.withDensity p) ≤
      integratedCosineForm μ p hp hpm f hfm hf F hF w := by
  have hlower := unitary_cosineSeries_lower hw hs U β hβ
  change algebraMap ℝ 𝓐 (-1 + β) ≤ cosineOperator μ F hF w at hlower
  have hnorm := levelNorm_integral μ p hp hpm f hfm hf
  rw [← hnorm.2, ← integral_const_mul, integratedCosineForm]
  refine integral_mono (hnorm.1.const_mul (-1 + β))
    (integratedCosineForm_integrable μ p hp hpm f hfm hf F hF w hw hs) ?_
  intro u
  have h := reQuadraticCLM_mono μ (g u) hlower
  rwa [Algebra.algebraMap_eq_smul_one, map_smul, reQuadraticCLM_one, smul_eq_mul] at h

theorem integratedCosineForm_comparison (w q : ℕ → ℝ)
    (hw : ∀ j, 0 ≤ w j) (hq : ∀ j, 0 ≤ q j) (hws : Summable w) (hqs : Summable q)
    (c : ℝ) (hc : ∀ θ ∈ Icc (-Real.pi) Real.pi,
      c * (1 - cosineSeries q θ) ≤ 1 - cosineSeries w θ) :
    let N := ∫ z, f z ^ 2 ∂μ.withDensity p
    c * (N - integratedCosineForm μ p hp hpm f hfm hf F hF q) ≤
      N - integratedCosineForm μ p hp hpm f hfm hf F hF w := by
  dsimp only
  have hcompare := unitary_cosineSeries_comparison hw hq hws hqs U c hc
  change c • (1 - cosineOperator μ F hF q) ≤ 1 - cosineOperator μ F hF w at hcompare
  have hnorm := levelNorm_integral μ p hp hpm f hfm hf
  have hwi := integratedCosineForm_integrable μ p hp hpm f hfm hf F hF w hw hws
  have hqi := integratedCosineForm_integrable μ p hp hpm f hfm hf F hF q hq hqs
  rw [← hnorm.2, integratedCosineForm, integratedCosineForm, ← integral_sub hnorm.1 hqi,
    ← integral_sub hnorm.1 hwi, ← integral_const_mul]
  refine integral_mono ((hnorm.1.sub hqi).const_mul c) (hnorm.1.sub hwi) ?_
  intro u
  have h := reQuadraticCLM_mono μ (g u) hcompare
  rwa [map_smul, map_sub, map_sub, reQuadraticCLM_one, smul_eq_mul] at h

end DensityLevels

end BreakingResonance

#print axioms BreakingResonance.densityTest_memLp
#print axioms BreakingResonance.lpComposition_re_inner
#print axioms BreakingResonance.levelCross_weighted
#print axioms BreakingResonance.levelNorm_integral
#print axioms BreakingResonance.integratedCosineForm_eq_tsum
#print axioms BreakingResonance.integratedCosineForm_lower
#print axioms BreakingResonance.integratedCosineForm_comparison
