import PersistencePays.GaussianCovarianceOperator

/-! The Gaussian quadratic entropy test with its full integrability range.
This yields coefficient two in the covariance inequality used for free transport. -/
noncomputable section
namespace BreakingResonance
open MeasureTheory ProbabilityTheory InformationTheory PersistencePays
open scoped ENNReal RealInnerProductSpace InnerProductSpace

theorem scalar_covariance_test_integrable (g a : ℝ) (hg : -1<g) :
    Integrable (fun x => Real.exp (gaussianCovarianceTest g a x)) (gaussianReal 0 1) := by
  rw [← stdGaussian_real]
  simp_rw [gaussianCovarianceTest_exp]
  exact (stdGaussian_quadratic_exp_integrable (E:=ℝ) ((1-g)/2)
    (by linarith) ((1+g)*a/2)).mul_const _

theorem scalar_covariance_test_normalized (g a : ℝ) (hg : -1<g) :
    (∫ x, Real.exp (gaussianCovarianceTest g a x) ∂gaussianReal 0 1)=1 := by
  rw [← stdGaussian_real]
  simp_rw [gaussianCovarianceTest_exp]
  rw [integral_mul_const,stdGaussian_quadratic_mgf_exp _ (by linarith),← Real.exp_add]
  have hd : 1-(1-g)/2=(1+g)/2 := by ring
  have hgne : 1+g ≠ 0 := by linarith
  rw [hd]
  norm_num only [Module.finrank_self, Nat.cast_one, Real.norm_eq_abs, sq_abs]
  convert Real.exp_zero using 1
  congr 1
  field_simp
  ring

variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem basis_covariance_test_integrable (b : OrthonormalBasis ι ℝ E)
    (g : ι → ℝ) (hg : ∀ i,-1<g i) (a : E) :
    Integrable (fun x => Real.exp (basisCovarianceTest b g a x)) (stdGaussian E) := by
  rw [stdGaussian_eq_map_pi_orthonormalBasis b]
  apply (integrable_map_measure ((basisCovarianceTest_measurable b g a).exp.aestronglyMeasurable)
    (show Measurable (fun x : ι → ℝ => ∑ i, x i • b i) by fun_prop).aemeasurable).mpr
  simp_rw [Function.comp_def,basisCovarianceTest_reconstruct]
  exact Integrable.fintype_prod (fun i => scalar_covariance_test_integrable (g i) _ (hg i))

theorem basis_covariance_test_normalized (b : OrthonormalBasis ι ℝ E)
    (g : ι → ℝ) (hg : ∀ i,-1<g i) (a : E) :
    (∫ x, Real.exp (basisCovarianceTest b g a x) ∂stdGaussian E)=1 := by
  rw [stdGaussian_eq_map_pi_orthonormalBasis b,integral_map
    (show Measurable (fun x : ι → ℝ => ∑ i, x i • b i) by fun_prop).aemeasurable
    ((basisCovarianceTest_measurable b g a).exp.aestronglyMeasurable)]
  simp_rw [basisCovarianceTest_reconstruct]
  rw [integral_fintype_prod_eq_prod (fun (i : ι) (x : ℝ) =>
    Real.exp (gaussianCovarianceTest (g i) ⟪b i,a⟫_ℝ x))]
  simp_rw [scalar_covariance_test_normalized _ _ (hg _)]
  simp

theorem basis_covariance_entropy (μ : Measure E) [IsProbabilityMeasure μ]
    (hm : MemLp id 2 μ) (hD : klDiv μ (stdGaussian E) ≠ ∞)
    (b : OrthonormalBasis ι ℝ E) (g : ι → ℝ) (hg : ∀ i,-1<g i) :
    let a := ∫ x,x ∂μ
    (∑ i,(1-g i)*(∫ x,⟪b i,x-a⟫_ℝ^2 ∂μ))/4 ≤
      (klDiv μ (stdGaussian E)).toReal-‖a‖^2/2-(∑ i,Real.log ((1+g i)/2))/2 := by
  dsimp only
  let a := ∫ x,x ∂μ
  have hi (i : ι) : Integrable (fun x => gaussianCovarianceTest (g i) ⟪b i,a⟫_ℝ ⟪b i,x⟫_ℝ) μ :=
    scalarCovarianceTest_integrable μ _ (inner_memLp_two μ hm (b i)) _ _
  have hF : Integrable (basisCovarianceTest b g a) μ := integrable_finsetSum _ (fun i _ => hi i)
  have hb := integral_le_klDiv_of_exp_integral_le_one μ (stdGaussian E) hD
    (basisCovarianceTest b g a) hF (basis_covariance_test_integrable b g hg a)
    (basis_covariance_test_normalized b g hg a).le
  unfold basisCovarianceTest at hb
  rw [integral_finsetSum _ (fun i _ => hi i)] at hb
  have he (i : ι) := scalarCovarianceTest_expectation μ (fun x => ⟪b i,x⟫_ℝ)
    (inner_memLp_two μ hm (b i)) (g i) ⟪b i,a⟫_ℝ (inner_mean μ hm (b i))
  simp_rw [he] at hb
  have hr (i : ι) : (1-g i)/4*(∫ x,(⟪b i,x⟫_ℝ-⟪b i,a⟫_ℝ)^2 ∂μ) =
      ((1-g i)*(∫ x,⟪b i,x-a⟫_ℝ^2 ∂μ))/4 := by
    simp only [inner_sub_right]
    ring
  simp_rw [hr] at hb
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib,← Finset.sum_div,
    ← Finset.sum_div,← Finset.sum_div,b.sum_sq_inner_right] at hb
  change (∑ i,(1-g i)*(∫ x,⟪b i,x-a⟫_ℝ^2 ∂μ))/4 ≤ _
  linarith

/-- Gaussian covariance entropy with the sharp coefficient used in the manuscript. -/
theorem basis_covariance_entropy_sharp (μ : Measure E) [IsProbabilityMeasure μ]
    (hm : MemLp id 2 μ) (hD : klDiv μ (stdGaussian E) ≠ ∞)
    (b : OrthonormalBasis ι ℝ E) (g : ι → ℝ) (hg : ∀ i,0<g i) :
    let a := ∫ x,x ∂μ
    (∑ i,(1-g i)*(∫ x,⟪b i,x-a⟫_ℝ^2 ∂μ)) ≤
      2*(klDiv μ (stdGaussian E)).toReal-‖a‖^2-(∑ i,Real.log (g i)) := by
  have hb := basis_covariance_entropy μ hm hD b (fun i => 2*g i-1)
    (fun i => by linarith [hg i])
  dsimp only at hb ⊢
  have he (i : ι) : (1+(2*g i-1))/2=g i := by ring
  have hf (i : ι) : (1-(2*g i-1))*(∫ x,⟪b i,x-(∫ y,y ∂μ)⟫_ℝ^2 ∂μ) =
      2*((1-g i)*(∫ x,⟪b i,x-(∫ y,y ∂μ)⟫_ℝ^2 ∂μ)) := by ring
  simp_rw [he,hf] at hb
  rw [← Finset.mul_sum] at hb
  linarith

/-- Basis-independent sharp covariance entropy bound. -/
theorem gaussian_covariance_entropy_sharp (μ : Measure E) [IsProbabilityMeasure μ]
    (hm : MemLp id 2 μ) (hD : klDiv μ (stdGaussian E) ≠ ∞)
    (G : E →ₗ[ℝ] E) (hG : G.IsSymmetric)
    (hpos : ∀ x:E,x ≠ 0 → 0<⟪x,G x⟫_ℝ) :
    covarianceContraction μ ((LinearMap.id : E →ₗ[ℝ] E)-G) ≤
      2*(klDiv μ (stdGaussian E)).toReal-‖∫ x,x ∂μ‖^2-Real.log (LinearMap.det G) := by
  let b := hG.eigenvectorBasis rfl
  let g := hG.eigenvalues rfl
  have hg : ∀ i,0<g i := symmetric_positive_eigenvalues G hG hpos
  have hcoord (z:E) (i:Fin (Module.finrank ℝ E)) : ⟪b i,G z⟫_ℝ=g i*⟪b i,z⟫_ℝ := by
    simpa only [OrthonormalBasis.repr_apply_apply,RCLike.ofReal_real_eq_id,id_eq,b,g] using
      hG.eigenvectorBasis_apply_self_apply rfl z i
  rw [covarianceContraction_basis μ hm G b g hcoord,hG.det_eq_prod_eigenvalues rfl]
  simp only [RCLike.ofReal_real_eq_id,id_eq]
  rw [Real.log_prod (fun i _ => (hg i).ne')]
  exact basis_covariance_entropy_sharp μ hm hD b g hg

end BreakingResonance
