import BreakingResonance.VerletWeightedEntropy
import BreakingResonance.ProposalMixture
import BreakingResonance.EnergyControl

/-! The rounded triangular endpoint mixture and the final constants in
Proposition 6.8. -/
noncomputable section
namespace BreakingResonance
open PersistencePays MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

variable {S : Type*} [MeasurableSpace S]

/-- On cell n, either endpoint has weight ω_n/T² after the fair Bernoulli draw. -/
def triangularEndpointLaw (μ : ℕ → ProbabilityMeasure S) (h : ℝ) (N : ℕ) : Measure S :=
  ∑ i ∈ (Finset.range N).product (Finset.range 2),
    ENNReal.ofReal (triangularWeight h N i.1 / ((N : ℝ) * h)^2) •
      (μ (i.1 + i.2) : Measure S)

theorem triangularEndpointLaw_kl_le (μ : ℕ → ProbabilityMeasure S) (π : Measure S)
    [IsProbabilityMeasure π] {h : ℝ} (hh : 0 < h) {N : ℕ} (hN : 0 < N)
    (hfinite : ∀ j ≤ N, klDiv (μ j : Measure S) π ≠ ∞) :
    klDiv (triangularEndpointLaw μ h N) π ≤
      ENNReal.ofReal ((∑ n ∈ Finset.range N, triangularWeight h N n *
        ((klDiv (μ n : Measure S) π).toReal + (klDiv (μ (n+1) : Measure S) π).toReal)) /
        ((N : ℝ) * h)^2) := by
  let T : ℝ := (N : ℝ) * h
  have hT : 0 < T := mul_pos (by exact_mod_cast hN) hh
  let w : ℕ × ℕ → ℝ := fun i => triangularWeight h N i.1 / T^2
  let s := (Finset.range N).product (Finset.range 2)
  have hw : ∀ i ∈ s, 0 ≤ w i := by
    intro i hi
    exact div_nonneg (triangularWeight_nonneg (Finset.mem_range.mp (Finset.mem_product.mp hi).1))
      (sq_nonneg T)
  have hw₁ : ∑ i ∈ s, w i = 1 := by
    dsimp only [s, w]
    rw [Finset.product_eq_sprod, Finset.sum_product]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [Finset.sum_add_distrib, ← Finset.sum_div, triangularWeight_sum]
    change T^2 / 2 / T^2 + T^2 / 2 / T^2 = 1
    field_simp
    ring
  have hf : ∀ i ∈ s, klDiv (μ (i.1 + i.2) : Measure S) π ≠ ∞ := by
    intro i hi
    rcases Finset.mem_product.mp hi with ⟨hn, hb⟩
    exact hfinite (i.1 + i.2) (by
      have h₁ := Finset.mem_range.mp hn
      have h₂ := Finset.mem_range.mp hb
      omega)
  have hKL := klDiv_finite_mixture_le s w hw hw₁ (fun i => μ (i.1 + i.2)) π hf
  change klDiv (triangularEndpointLaw μ h N) π ≤ _ at hKL
  refine hKL.trans_eq (congrArg ENNReal.ofReal ?_)
  dsimp only [s, w]
  rw [Finset.product_eq_sprod, Finset.sum_product, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro n _
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, add_zero]
  ring

/-- The same law grouped by numerical integration time, with the weights in
equation (5.4). There are N = k+1 cells and N+1 distinct endpoints. -/
theorem triangularEndpointLaw_eq_triangularWeights (μ : ℕ → ProbabilityMeasure S)
    {h : ℝ} (hh : 0 < h) (k : ℕ) :
    let N := k + 1
    triangularEndpointLaw μ h N =
      ENNReal.ofReal ((2*(N : ℝ)-1)/(2*(N : ℝ)^2)) • (μ 0 : Measure S) +
      (∑ j ∈ Finset.range k,
        ENNReal.ofReal (2*((N : ℝ)-(j+1 : ℕ))/(N : ℝ)^2) • (μ (j+1) : Measure S)) +
      ENNReal.ofReal (1/(2*(N : ℝ)^2)) • (μ N : Measure S) := by
  dsimp only
  let w : ℕ → ℝ := fun j => triangularWeight h (k+1) j / (((k+1 : ℕ) : ℝ)*h)^2
  have hw (j : ℕ) : w j = (((k+1 : ℕ) : ℝ)-j-1/2) / ((k+1 : ℕ) : ℝ)^2 := by
    have hk : (0 : ℝ) < ((k+1 : ℕ) : ℝ) := by positivity
    dsimp only [w, triangularWeight]
    field_simp
  have h0 : w 0 = (2*((k+1 : ℕ) : ℝ)-1)/(2*((k+1 : ℕ) : ℝ)^2) := by
    rw [hw, Nat.cast_zero]
    ring
  have hk : w k = 1/(2*((k+1 : ℕ) : ℝ)^2) := by
    rw [hw]
    have hn : ((k+1 : ℕ) : ℝ) - (k : ℝ) = 1 := by push_cast; ring
    rw [hn]
    ring
  have hinterior (j : ℕ) :
      w (j+1) + w j = 2*(((k+1 : ℕ) : ℝ)-(j+1 : ℕ))/((k+1 : ℕ) : ℝ)^2 := by
    rw [hw (j+1), hw j]
    push_cast
    ring
  have hnonneg (j : ℕ) (hj : j < k+1) : 0 ≤ w j :=
    div_nonneg (triangularWeight_nonneg hj) (sq_nonneg _)
  unfold triangularEndpointLaw
  rw [Finset.product_eq_sprod, Finset.sum_product]
  change (∑ j ∈ Finset.range (k+1), ∑ b ∈ Finset.range 2,
    ENNReal.ofReal (w j) • (μ (j+b) : Measure S)) = _
  simp only [Finset.sum_range_succ _ 1, Finset.sum_range_succ _ 0,
    Finset.sum_range_zero, zero_add, Nat.add_zero]
  rw [Finset.sum_add_distrib, Finset.sum_range_succ' _ k, Finset.sum_range_succ _ k]
  calc
    _ = ENNReal.ofReal (w 0) • (μ 0 : Measure S) +
        (∑ j ∈ Finset.range k, (ENNReal.ofReal (w (j+1)) • (μ (j+1) : Measure S) +
          ENNReal.ofReal (w j) • (μ (j+1) : Measure S))) +
        ENNReal.ofReal (w k) • (μ (k+1) : Measure S) := by
      rw [Finset.sum_add_distrib]
      ac_rfl
    _ = _ := by
      rw [h0, hk]
      congr 2
      apply Finset.sum_congr rfl
      intro j hj
      have hj' := Finset.mem_range.mp hj
      rw [← add_smul, ← ENNReal.ofReal_add
        (hnonneg (j+1) (by omega)) (hnonneg j (by omega)), hinterior]

/-- Divide the signed weighted estimate by 3T² using the energy and
transport-entropy bounds from the proof of Proposition 6.8. -/
theorem proposal_entropy_bound_from_weighted_sums
    {m L T h R E₀ aT W Iend Imod Qweighted ΔU Qsum Qint : ℝ}
    (hm : 0 < m) (hmL : m ≤ L) (hT : 0 < T) (hTlow : 2 / Real.sqrt m ≤ T)
    (hR : 0 ≤ R)
    (hW : W ≤ E₀ / m)
    (hImod : Imod ≤ aT * T^2) (hQweighted : Qweighted ≤ 2 * (h^2 * L * R) * T^2)
    (hΔU : ΔU ≤ 2 * R) (hQsum : 0 ≤ Qsum) (hQint : 0 ≤ Qint)
    (hw : 3 * Iend ≤ W + 5/2 * E₀ * T^2 + 5 * Imod + 3 * Qweighted +
      h^2/4 * ΔU - h^2/12 * Qsum - Qint) :
    Iend / T^2 ≤ (5/6 + 1 / (3 * m * T^2)) * E₀ + 5/3 * aT + 49/24 * (h^2 * L * R) := by
  have hmroot := Real.sqrt_pos.2 hm
  have htime : 2 ≤ T * Real.sqrt m := (div_le_iff₀ hmroot).mp hTlow
  have htimeSq : 4 ≤ L * T^2 := by
    have h₁ := mul_le_mul htime htime (by norm_num : (0 : ℝ) ≤ 2)
      (mul_nonneg hT.le hmroot.le)
    have h₂ := mul_le_mul_of_nonneg_right hmL (sq_nonneg T)
    have h₃ : 4 ≤ T^2 * m := by
      rw [← Real.sq_sqrt hm.le, ← mul_pow]
      nlinarith only [h₁]
    linarith only [h₂, h₃]
  have hΔ := mul_le_mul_of_nonneg_left hΔU (by positivity : 0 ≤ h^2/4)
  have hq : 0 ≤ h^2/12 * Qsum := by positivity
  have hr := mul_le_mul_of_nonneg_left htimeSq (by positivity : 0 ≤ h^2*R/8)
  apply (mul_le_mul_iff_right₀ (show 0 < 3 * T^2 by positivity)).mp
  calc
    3 * T^2 * (Iend / T^2) = 3 * Iend := by field_simp
    _ ≤ E₀/m + 5/2 * E₀ * T^2 + 5 * (aT*T^2) +
        3 * (2 * (h^2*L*R) * T^2) + (h^2*L*R)*T^2/8 := by
      linarith only [hw, hW, hImod, hQweighted, hΔ, hq, hQint, hr]
    _ = 3 * T^2 * ((5/6 + 1 / (3*m*T^2)) * E₀ + 5/3*aT + 49/24*(h^2*L*R)) := by
      field_simp
      ring

section Verlet

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The identity and cubic remainder bound of Lemma 6.1, cited from
Persistence Pays, Lemma 2.1. -/
def PPModifiedEnergy (U : E → ℝ) (LH : ℝ) : Prop :=
  ∀ (h : ℝ), 0 < h → ∀ z : E × E,
    let g := gradient U
    let z' := verlet g h z
    let r := trapezoidDefect U g z.1 z'.1
    modifiedEnergy U g h z' - modifiedEnergy U g h z = r ∧
      |r| ≤ LH * h^3 * ‖flightVelocity g h z‖^3 / 12

omit [MeasurableSpace E] [BorelSpace E] in
/-- Lemma 6.1 under the paper's Hessian regularity assumption. -/
theorem ppModifiedEnergy_of_hessian {U : E → ℝ} {LH : ℝ}
    (hU : ContDiff ℝ 2 U) (hLip : A2 U LH) : PPModifiedEnergy U LH := by
  intro h hh z
  have hgrad (x : E) : HasGradientAt U (gradient U x) x :=
    ((hU.differentiable (by norm_num)) x).hasGradientAt
  have hD := contDiff_gradient_of_twice_contDiff U hU
  have hHess (x : E) : HasFDerivAt (gradient U) (hessian U x) x :=
    ((hD.differentiable (by norm_num)) x).hasFDerivAt
  have hA : Continuous (hessian U) := hD.continuous_fderiv (by norm_num)
  dsimp only
  constructor
  · exact modifiedEnergy_increment U (gradient U) h z
  · have hr := verlet_trapezoidDefect_lipschitz_bound U (gradient U) (hessian U)
      hgrad hHess hA LH h hh.le hLip.lipschitz z
    convert hr using 1
    ring

/-- Lemma 6.3 as a hypothesis, stated in terms of half the squared
2-Wasserstein distance and the Gibbs law on position space. -/
def TalagrandBound {U : E → ℝ} {m L : ℝ} (a : A1 U m L) : Prop :=
  ∀ ν : ProbabilityMeasure E, klDiv (ν : Measure E) (positionGibbs U) ≠ ∞ →
    (QuadraticTransport.cost ν a.targetProbability).toReal / 2 ≤
      (klDiv (ν : Measure E) (positionGibbs U)).toReal / m

theorem energy_shell_memLp {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (hmin : U a.minimizer = 0) {R : ℝ}
    (μ : ProbabilityMeasure (E × E))
    (hshell : ∀ᵐ z ∂(μ : Measure (E × E)), phaseEnergy U z ≤ R) :
    MemLp id 2 (μ : Measure (E × E)) := by
  apply MemLp.mono_exponent _ le_top
  apply memLp_top_of_bound measurable_id.aestronglyMeasurable
    (max (‖a.minimizer‖ + Real.sqrt (2*R/m)) (Real.sqrt (2*R)))
  filter_upwards [hshell] with z hz
  have hp := a.quadratic_lower_at_minimizer z.1
  rw [hmin, zero_add] at hp
  rw [phaseEnergy_eq_norm] at hz
  have hu : U z.1 ≤ R := by linarith only [hz, sq_nonneg ‖z.2‖]
  have hx : ‖z.1 - a.minimizer‖ ≤ Real.sqrt (2*R/m) := by
    apply Real.le_sqrt_of_sq_le
    apply (le_div_iff₀ a.m_pos).mpr
    linarith only [hp, hu]
  have hv : ‖z.2‖ ≤ Real.sqrt (2*R) := by
    apply Real.le_sqrt_of_sq_le
    have hU : 0 ≤ U z.1 := hmin ▸ a.minimizer_le z.1
    linarith only [hz,hU]
  have hx' : ‖z.1‖ ≤ ‖a.minimizer‖ + Real.sqrt (2*R/m) := by
    have htri := norm_sub_le (z.1 - a.minimizer) (-a.minimizer)
    simp only [sub_neg_eq_add, sub_add_cancel, norm_neg] at htri
    linarith only [hx,htri]
  exact max_le_max hx' hv

omit [MeasurableSpace E] [BorelSpace E] in
theorem cellRemainder_nonneg {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (h σ : ℝ) (z : E × E) : 0 ≤ cellRemainder U (gradient U) h σ z := by
  have hb := a.strong_lower_bound z.1 (z.1 + σ • flightVelocity (gradient U) h z)
  rw [add_sub_cancel_left, inner_smul_right] at hb
  dsimp only [cellRemainder]
  linarith only [hb, show 0 ≤ m/2 * ‖σ • flightVelocity (gradient U) h z‖^2 by
    positivity [a.m_pos]]

omit [MeasurableSpace E] [BorelSpace E] in
theorem cellRemainder_le {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (h σ : ℝ) (z : E × E) :
    cellRemainder U (gradient U) h σ z ≤
      L/2 * σ^2 * ‖flightVelocity (gradient U) h z‖^2 := by
  have hb := potential_descent_bound U (gradient U) (hessian U) a.hasGradientAt
    a.hasHessianAt a.continuous_hessian L a.upper
    z.1 (z.1 + σ • flightVelocity (gradient U) h z)
  rw [add_sub_cancel_left, inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at hb
  dsimp only [cellRemainder]
  linarith only [hb]

/-- Proposition 6.8 for the finite mixture that puts weight ω_n/T² on
each endpoint of cell n. The initial law is supported on the energy shell.
The potential is normalized to vanish at its minimizer as in Section 6. -/
theorem verlet_triangular_proposal_entropy (hPP : PPInterpolation E)
    {U : E → ℝ} {m L LH : ℝ} (a : A1 U m L) (hLH : 0 ≤ LH)
    (_hhess : A2 U LH) (hPPenergy : PPModifiedEnergy U LH)
    (hTI : TalagrandBound a) (hmin : U a.minimizer = 0)
    {h R : ℝ} (hh : 0 < h) (hR : 1 ≤ R) (hstep : h * Real.sqrt L ≤ 1)
    (N : ℕ) (hTlow : 2 / Real.sqrt m ≤ (N : ℝ) * h)
    (hbudget : 2 * (LH * ((N : ℝ) * h) * h^2 * R * Real.sqrt R) + (h^2 * L * R)/2 ≤ R)
    (μ : ProbabilityMeasure (E × E))
    (hshell : ∀ᵐ z ∂(μ : Measure (E × E)), phaseEnergy U z ≤ R)
    (hK : klDiv (μ : Measure (E × E)) (phaseGibbs U) ≠ ∞)
    (hc : ∀ᵐ x ∂(μ : Measure (E × E)).fst,
      conditionalMeanVelocity (μ : Measure (E × E)) x = 0) :
    let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
    let μx := fun j : ℕ => (⟨(trajectoryLaw (gradient U) hg μ h j : Measure (E × E)).fst,
      inferInstance⟩ : ProbabilityMeasure E)
    let T := (N : ℝ) * h
    klDiv (triangularEndpointLaw μx h N) (positionGibbs U) ≤ ENNReal.ofReal
      ((5/6 + 1/(3*m*T^2)) * (klDiv (μ : Measure (E × E)) (phaseGibbs U)).toReal +
        5/3 * (LH*T*h^2*R*Real.sqrt R) + 49/24 * (h^2*L*R)) := by
  dsimp only
  let : IsProbabilityMeasure (positionGibbs U) := a.gibbs_isProbabilityMeasure
  let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
  let ζ := fun j => (trajectoryLaw (gradient U) hg μ h j : Measure (E × E))
  let μx := fun j => (⟨(ζ j).fst,inferInstance⟩ : ProbabilityMeasure E)
  let T := (N : ℝ) * h
  let aT := LH*T*h^2*R*Real.sqrt R
  let bH := h^2*L*R
  have hR₀ : 0 ≤ R := by linarith
  have hU (x : E) : 0 ≤ U x := hmin ▸ a.minimizer_le x
  have hT : 0 < T := (div_pos (by norm_num) (Real.sqrt_pos.mpr a.m_pos)).trans_le hTlow
  have hN : 0 < N := by
    by_contra! hn
    have hz : N = 0 := Nat.eq_zero_of_le_zero hn
    simp [T, hz] at hT
  have hstep' : h^2*L ≤ 1 := by
    rw [← Real.sq_sqrt a.L_pos.le, ← mul_pow]
    have hl : 0 ≤ h*Real.sqrt L := by positivity
    nlinarith only [hstep, hl, mul_le_mul hstep hstep hl zero_le_one]
  have hμ := energy_shell_memLp a hmin μ hshell
  let E₀ := (klDiv (μ : Measure (E × E)) (phaseGibbs U)).toReal
  let Epos := fun j => (klDiv (ζ j).fst (positionGibbs U)).toReal
  let b := fun j => (∫ z, modifiedEnergy U (gradient U) h z ∂ζ j) -
    (∫ z, phaseEnergy U z ∂(μ : Measure (E × E)))
  let Q := fun j => ∫ z, cellRemainder U (gradient U) h h z ∂ζ j
  let u := fun j => ∫ z, U z.1 ∂ζ j
  have hm (j : ℕ) : MemLp id 2 (ζ j) := trajectoryLaw_memLp a μ hμ h j
  have hmap (j : ℕ) : Measurable (fun z => trajectory (gradient U) h z j) :=
    (trajectory_measurePreserving (gradient U) hg h j).measurable
  have hrem (z : E × E) :
      |modifiedEnergy U (gradient U) h (verlet (gradient U) h z) -
        modifiedEnergy U (gradient U) h z| ≤ LH/12 * h^3 * ‖flightVelocity (gradient U) h z‖^3 := by
    obtain ⟨heq, hb⟩ := hPPenergy h hh z
    rw [heq]
    convert hb using 1
    ring
  have henergy (j : ℕ) (hj : j ≤ N) :
      ∀ᵐ z ∂(μ : Measure (E × E)),
        phaseEnergy U (trajectory (gradient U) h z j) ≤ 2*R ∧
        ‖flightVelocity (gradient U) h (trajectory (gradient U) h z j)‖^2 ≤ 8*R ∧
        modifiedEnergy U (gradient U) h (trajectory (gradient U) h z j) - phaseEnergy U z ≤ 2*aT := by
    filter_upwards [hshell] with z hz
    obtain ⟨_, hen, _, hv, hb⟩ := verlet_energy_control_with_modified_error_of_remainder U
      (gradient U) (hessian U) a.hasGradientAt a.hasHessianAt a.continuous_hessian
      L LH h R a.L_pos hLH hh.le hR₀ hU a.upper hrem hstep' N hbudget z hz j hj
    exact ⟨hen,hv,hb⟩
  have hfin (j : ℕ) : klDiv (ζ j).fst (positionGibbs U) ≠ ∞ :=
    a.position_entropy_finite (ζ j) (trajectoryLaw_entropy_finite a μ hμ hK h j)
  have hW : positionCost (μ : Measure (E × E)) a.targetProbability ≤ E₀/m := by
    apply (hTI ⟨(μ : Measure (E × E)).fst, inferInstance⟩
      (a.position_entropy_finite (μ : Measure (E × E)) hK)).trans
    apply div_le_div_of_nonneg_right _ a.m_pos.le
    apply ENNReal.toReal_mono hK
    rw [show phaseGibbs U = (positionGibbs U).prod (stdGaussian E) from rfl,
      klDiv_product_reference_decomposition]
    exact le_add_right le_rfl
  have hbn (j : ℕ) (hj : j < N) : b j ≤ 2*aT := by
    have hp : Integrable (phaseEnergy U) (ζ j) := a.phaseEnergy_integrable (hm j)
    have hf : Integrable (modifiedEnergy U (gradient U) h) (ζ j) := by
      have he := (modifiedEnergy_difference_integrable a (ζ j) (hm j) h).add hp
      simpa only [Pi.add_def, sub_add_cancel] using he
    have hf' := hf.comp_aemeasurable (hmap j).aemeasurable
    have hi : Integrable (phaseEnergy U) (μ : Measure (E × E)) := a.phaseEnergy_integrable hμ
    have he := integral_mono_ae (hf'.sub hi) (integrable_const (2*aT))
      ((henergy j hj.le).mono (fun _ hz => hz.2.2))
    simp only [Pi.sub_apply] at he
    rw [integral_sub hf' hi, integral_const, probReal_univ, one_smul] at he
    have hchange : (∫ z, modifiedEnergy U (gradient U) h z ∂ζ j) =
        ∫ z, (modifiedEnergy U (gradient U) h ∘ fun z => trajectory (gradient U) h z j) z
          ∂(μ : Measure (E × E)) :=
      integral_map (hmap j).aemeasurable hf.aestronglyMeasurable
    dsimp only [b]
    rw [hchange]
    exact he
  have hQbound (j : ℕ) (hj : j < N) : Q j ≤ 4*bH := by
    have hme : Measurable (flightVelocity (gradient U) h) :=
      measurable_snd.sub ((hg.comp measurable_fst).const_smul (h/2))
    have hv : ∀ᵐ z ∂ζ j, ‖flightVelocity (gradient U) h z‖^2 ≤ 8*R :=
      (ae_map_iff (hmap j).aemeasurable (measurableSet_le (by fun_prop) measurable_const)).2
        ((henergy j hj.le).mono (fun _ hz => hz.2.1))
    have hb : ∀ᵐ z ∂ζ j, cellRemainder U (gradient U) h h z ≤ 4*bH := by
      filter_upwards [hv] with z hz
      have hmul := mul_le_mul_of_nonneg_left hz
        (show 0 ≤ L/2*h^2 by positivity [a.L_pos])
      dsimp only [bH]
      linarith only [cellRemainder_le a h h z, hmul]
    have he := integral_mono_ae (cellRemainder_integrable a (ζ j) (hm j) h h)
      (integrable_const (4*bH)) hb
    simpa only [Q, integral_const, probReal_univ, one_smul] using he
  have hImod : (∑ j ∈ Finset.range N, triangularWeight h N j * b j) ≤ aT*T^2 := by
    calc
      _ ≤ ∑ j ∈ Finset.range N, triangularWeight h N j * (2*aT) :=
        Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_left
          (hbn j (Finset.mem_range.mp hj)) (triangularWeight_nonneg (Finset.mem_range.mp hj))
      _ = _ := by rw [← Finset.sum_mul, triangularWeight_sum]; dsimp only [T]; ring
  have hQweighted : (∑ j ∈ Finset.range N, triangularWeight h N j * Q j) ≤ 2*bH*T^2 := by
    calc
      _ ≤ ∑ j ∈ Finset.range N, triangularWeight h N j * (4*bH) :=
        Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_left
          (hQbound j (Finset.mem_range.mp hj)) (triangularWeight_nonneg (Finset.mem_range.mp hj))
      _ = _ := by rw [← Finset.sum_mul, triangularWeight_sum]; dsimp only [T]; ring
  have hUdiff : u N - u 0 ≤ 2*R := by
    have hUN : ∀ᵐ z ∂ζ N, U z.1 ≤ 2*R := by
      apply (ae_map_iff (hmap N).aemeasurable
        (measurableSet_le (a.twice_contDiff.continuous.measurable.comp measurable_fst)
          measurable_const)).2
      filter_upwards [henergy N le_rfl] with z hz
      change U (trajectory (gradient U) h z N).1 ≤ 2*R
      have hen := hz.1
      rw [phaseEnergy_eq_norm] at hen
      linarith only [hen, sq_nonneg ‖(trajectory (gradient U) h z N).2‖]
    have hUNint := integral_mono_ae (a.potential_integrable (hm N).fst)
      (integrable_const (2*R)) hUN
    rw [integral_const, probReal_univ, one_smul] at hUNint
    have hU0 : 0 ≤ u 0 := integral_nonneg (fun z => hU z.1)
    change u N ≤ 2*R at hUNint
    linarith only [hU0,hUNint]
  have hQsum : 0 ≤ ∑ j ∈ Finset.range N, Q j :=
    Finset.sum_nonneg fun j _ => integral_nonneg (cellRemainder_nonneg a h h)
  have hQint : 0 ≤ ∑ j ∈ Finset.range N, ∫ σ in (0 : ℝ)..h,
      (((N : ℝ) - j) * h - σ) * (∫ z, cellRemainder U (gradient U) h σ z ∂ζ j) := by
    apply Finset.sum_nonneg
    intro j hj
    apply intervalIntegral.integral_nonneg hh.le
    intro σ hσ
    have hj' : (j : ℝ) + 1 ≤ N := by exact_mod_cast Finset.mem_range.mp hj
    have hmul := mul_le_mul_of_nonneg_right (show 1 ≤ (N : ℝ) - j by linarith) hh.le
    exact mul_nonneg (by linarith only [hmul,hσ.2])
      (integral_nonneg (cellRemainder_nonneg a h σ))
  have hw := verlet_weighted_entropy_with_initial_entropy hPP a μ hμ hK hc hh N
  have hbound := proposal_entropy_bound_from_weighted_sums a.m_pos a.m_le_L hT hTlow
    hR₀ hW hImod hQweighted hUdiff hQsum hQint hw
  exact (triangularEndpointLaw_kl_le μx (positionGibbs U) hh hN (fun j _ => hfin j)).trans
    (ENNReal.ofReal_le_ofReal hbound)

end Verlet

end BreakingResonance

#print axioms BreakingResonance.triangularEndpointLaw_kl_le
#print axioms BreakingResonance.proposal_entropy_bound_from_weighted_sums

#print axioms BreakingResonance.verlet_triangular_proposal_entropy

#print axioms BreakingResonance.triangularEndpointLaw_eq_triangularWeights
