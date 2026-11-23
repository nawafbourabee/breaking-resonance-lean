import BreakingResonance.LowerExpandingProbability

noncomputable section

open Set PersistencePays
open scoped RealInnerProductSpace Gradient

namespace BreakingResonance

variable {ι : Type*} [Fintype ι]

def separablePotential (a b : ι → ℝ) (x : EuclideanSpace ℝ ι) : ℝ :=
  ∑ i, fastPotential (a i) (b i) (x i)

def separableForce (a b : ι → ℝ) (x : EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 (fun i => fastGradient (a i) (b i) (x i))

theorem separablePotential_gradient (a b : ι → ℝ) (x : EuclideanSpace ℝ ι) :
    HasGradientAt (separablePotential a b) (separableForce a b x) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have h (i : ι) :
      HasFDerivAt (fun y : EuclideanSpace ℝ ι => fastPotential (a i) (b i) (y i))
        (fastGradient (a i) (b i) (x i) • (PiLp.proj (𝕜 := ℝ) (p := 2) (β := fun _ : ι => ℝ) i)) x := by
    exact (fastPotential_hasDerivAt (a i) (b i) (x i)).comp_hasFDerivAt x
      (PiLp.proj (𝕜 := ℝ) (p := 2) (β := fun _ : ι => ℝ) i).hasFDerivAt
  have hs := HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ => h i)
  have he : InnerProductSpace.toDual ℝ (EuclideanSpace ℝ ι) (separableForce a b x) =
      ∑ i, fastGradient (a i) (b i) (x i) • (PiLp.proj (𝕜 := ℝ) (p := 2) (β := fun _ : ι => ℝ) i) := by
    apply ContinuousLinearMap.ext
    intro y
    rw [InnerProductSpace.toDual_apply_apply,PiLp.inner_apply]
    simp [separableForce,ContinuousLinearMap.sum_apply,PiLp.proj_apply,Real.inner_apply,mul_comm]
  rw [he]
  exact hs

theorem separableForce_lipschitz (a b : ι → ℝ) (hab : ∀ i, a i ≤ b i)
    (ha : ∀ i, 0 ≤ a i) (L : NNReal) (hbL : ∀ i, b i ≤ L) :
    LipschitzWith L (separableForce a b) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  have h (i : ι) :
      |fastGradient (a i) (b i) (x i)-fastGradient (a i) (b i) (y i)| ≤ (L:ℝ)*|x i-y i| := by
    let ci : NNReal := ⟨b i, (ha i).trans (hab i)⟩
    have hc := (lipschitzWith_iff_dist_le_mul.mp (fastGradient_lipschitz (curvPos := ci) (ha i) (hab i)))
      (x i) (y i)
    rw [Real.dist_eq,Real.dist_eq] at hc
    exact hc.trans (mul_le_mul_of_nonneg_right (hbL i) (abs_nonneg _))
  apply (sq_le_sq₀ dist_nonneg (by positivity)).mp
  calc
    dist (separableForce a b x) (separableForce a b y)^2 =
        ∑ i, |fastGradient (a i) (b i) (x i)-fastGradient (a i) (b i) (y i)|^2 := by
      simp [dist_eq_norm,EuclideanSpace.real_norm_sq_eq,separableForce,sq_abs]
    _ ≤ ∑ i, ((L:ℝ)*|x i-y i|)^2 := Finset.sum_le_sum fun i _ =>
      (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr (h i)
    _ = ((L:ℝ)*dist x y)^2 := by
      simp [dist_eq_norm,EuclideanSpace.real_norm_sq_eq,mul_pow,Finset.mul_sum,sq_abs]

theorem separablePotential_strongConvex (a b : ι → ℝ) (m : ℝ)
    (ha : ∀ i, m ≤ a i) (hab : ∀ i, a i ≤ b i) :
    StrongConvexOn univ m (separablePotential a b) := by
  refine ⟨convex_univ,?_⟩
  intro x _ y _ u v hu hv huv
  have h (i : ι) := ((fastPotential_strongConvex (hab i)).mono (ha i)).2
    (mem_univ (x i)) (mem_univ (y i)) hu hv huv
  change separablePotential a b (u • x+v • y) ≤
    u*separablePotential a b x+v*separablePotential a b y-u*v*(m/2*‖x-y‖^2)
  unfold separablePotential
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [PiLp.add_apply,PiLp.smul_apply,PiLp.sub_apply,smul_eq_mul,
    Finset.mul_sum,← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro i _
  have hi := h i
  change fastPotential (a i) (b i) (u*x i+v*y i) ≤
    u*fastPotential (a i) (b i) (x i)+v*fastPotential (a i) (b i) (y i)-
      u*v*(m/2*‖x i-y i‖^2) at hi
  simpa [Real.norm_eq_abs,sq_abs,mul_assoc] using hi

theorem separableEnergy (a b : ι → ℝ) (z : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
    phaseEnergy (separablePotential a b) z =
      ∑ i, phaseEnergy (fastPotential (a i) (b i)) (z.1 i,z.2 i) := by
  simp only [phaseEnergy_eq_norm,EuclideanSpace.real_norm_sq_eq,separablePotential,
    Real.norm_eq_abs,sq_abs]
  rw [Finset.sum_add_distrib,Finset.sum_div]

theorem separableVerlet (a b : ι → ℝ) (h : ℝ)
    (z : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) (i : ι) :
    ((verlet (separableForce a b) h z).1 i,(verlet (separableForce a b) h z).2 i) =
      verlet (fastGradient (a i) (b i)) h (z.1 i,z.2 i) := by
  rfl

theorem separableTrajectory (a b : ι → ℝ) (h : ℝ)
    (z : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) (n : ℕ) (i : ι) :
    ((trajectory (separableForce a b) h z n).1 i,
      (trajectory (separableForce a b) h z n).2 i) =
       trajectory (fastGradient (a i) (b i)) h (z.1 i,z.2 i) n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [trajectory_succ,trajectory_succ,separableVerlet,ih]

end BreakingResonance

#print axioms BreakingResonance.separablePotential_gradient
#print axioms BreakingResonance.separableForce_lipschitz
#print axioms BreakingResonance.separablePotential_strongConvex
#print axioms BreakingResonance.separableEnergy
#print axioms BreakingResonance.separableTrajectory
