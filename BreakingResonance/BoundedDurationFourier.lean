import BreakingResonance.RoundedCountCells
import BreakingResonance.FiniteFourierIdentities

/-! The actual uniformly and triangularly distributed durations and their
rounded cosine coefficients. -/
noncomputable section
namespace BreakingResonance
open MeasureTheory Set
open scoped ENNReal

/-- The uniform duration law on [0,T]. The endpoint T has zero mass. -/
def uniformDurationLaw (T : ℝ) : Measure ℝ :=
  ENNReal.ofReal (1/T) • volume.restrict (Ico 0 T)

theorem uniformDuration_probability {T : ℝ} (hT : 0 < T) :
    IsProbabilityMeasure (uniformDurationLaw T) where
  measure_univ := by
    rw [uniformDurationLaw, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_univ,
      Real.volume_Ico, sub_zero, ← ENNReal.ofReal_mul (by positivity),
      one_div_mul_cancel hT.ne', ENNReal.ofReal_one]

theorem uniformDuration_ae {T : ℝ} :
    ∀ᵐ τ ∂uniformDurationLaw T, 0 ≤ τ ∧ τ < T :=
  Measure.ae_smul_measure (ae_restrict_mem measurableSet_Ico) _

theorem uniformDuration_cellMass {h : ℝ} (hh : 0 < h) {N j : ℕ} (hj : j < N) :
    uniformDurationLaw ((N : ℝ)*h) (Ico ((j : ℝ)*h) (((j : ℝ)+1)*h)) =
      ENNReal.ofReal (1/(N : ℝ)) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.zero_lt_of_lt hj
  have hj' : (j : ℝ)+1 ≤ N := by exact_mod_cast hj
  have hsub : Ico ((j : ℝ)*h) (((j : ℝ)+1)*h) ⊆ Ico 0 ((N : ℝ)*h) :=
    fun _ ht => ⟨(mul_nonneg (Nat.cast_nonneg _) hh.le).trans ht.1,
      ht.2.trans_le (mul_le_mul_of_nonneg_right hj' hh.le)⟩
  rw [uniformDurationLaw, Measure.smul_apply, smul_eq_mul, Measure.restrict_eq_self _ hsub,
    Real.volume_Ico, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp [hh.ne', hN.ne']
  ring

/-- Each cell contributes its mass times the mean cosine at its endpoints. -/
theorem roundedDuration_cosine_cells (h : ℝ) (hh : 0 < h) (N : ℕ) (ρ : Measure ℝ)
    [IsProbabilityMeasure ρ] (hs : ∀ᵐ τ ∂ρ, 0 ≤ τ ∧ τ < (N : ℝ)*h) (θ : ℝ) :
    cosineSeries (countLawWeight (roundedDurationLaw h ρ)) θ =
      ∑ j ∈ Finset.range N, (ρ (Ico ((j : ℝ)*h) (((j : ℝ)+1)*h))).toReal * cellCosine θ j := by
  rw [countLaw_cosineSeries_eq_integral_cos, roundedDuration_eq_cell_sum h hh N ρ hs]
  let f (j : ℕ) := Real.cos ((j : ℝ)*θ)
  let w (j : ℕ) := (1/2 : ℝ≥0∞) * ρ (Ico ((j : ℝ)*h) (((j : ℝ)+1)*h))
  have hw (j : ℕ) : w j ≠ ∞ :=
    ENNReal.mul_ne_top (by norm_num) (measure_ne_top _ _)
  have hi (j b : ℕ) : Integrable f (w j • Measure.dirac (j+b)) :=
    (integrable_dirac (by simp)).smul_measure (hw j)
  rw [integral_finsetSum_measure (fun j _ => integrable_finsetSum_measure.2 (fun b _ => hi j b))]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_finsetSum_measure (fun b _ => hi j b)]
  simp only [integral_smul_measure, integral_dirac, smul_eq_mul, Finset.sum_range_succ,
    Finset.sum_range_zero, Nat.add_zero, zero_add]
  simp only [w, f, Nat.cast_add, Nat.cast_one, cellCosine, ENNReal.toReal_mul,
    ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat]
  ring

theorem triangularCount_cosine_numerator {h : ℝ} (hh : 0 < h) {N : ℕ} (hN : 0 < N) (θ : ℝ) :
    cosineSeries (countLawWeight (triangularCountLaw h N)) θ =
      triangularCosineNumerator θ N / (N : ℝ)^2 := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  let : IsProbabilityMeasure (triangularDurationLaw ((N : ℝ)*h)) :=
    triangularDuration_probability (mul_pos hNr hh)
  unfold triangularCountLaw
  rw [roundedDuration_cosine_cells h hh N _ triangularDuration_ae, triangularCosineNumerator,
    Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  have hjN := Finset.mem_range.mp hj
  rw [triangularDuration_cellMass hh hjN, ENNReal.toReal_ofReal
    (div_nonneg (mul_nonneg (by norm_num) (triangularWeight_nonneg hjN)) (sq_nonneg _))]
  unfold triangularWeight
  field_simp [hh.ne', hNr.ne']

theorem uniformCount_cosine_numerator {h : ℝ} (hh : 0 < h) {N : ℕ} (hN : 0 < N) (θ : ℝ) :
    cosineSeries (countLawWeight (roundedDurationLaw h (uniformDurationLaw ((N : ℝ)*h)))) θ =
      (∑ j ∈ Finset.range N, cellCosine θ j) / (N : ℝ) := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  let : IsProbabilityMeasure (uniformDurationLaw ((N : ℝ)*h)) :=
    uniformDuration_probability (mul_pos hNr hh)
  rw [roundedDuration_cosine_cells h hh N _ uniformDuration_ae, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  rw [uniformDuration_cellMass hh (Finset.mem_range.mp hj), ENNReal.toReal_ofReal (by positivity)]
  ring

/-- The ratio B_N from Appendix C, evaluated at half the count frequency. -/
def boundedDurationRatio (N : ℕ) (u : ℝ) : ℝ :=
  (Real.cos u * Real.sin ((N : ℝ)*u))/((N : ℝ)*Real.sin u)

theorem triangularCount_cosine_ratio {h : ℝ} (hh : 0 < h) {N : ℕ} (hN : 0 < N)
    {u : ℝ} (hu : 0 < u) (huπ : u < Real.pi/2) :
    cosineSeries (countLawWeight (triangularCountLaw h N)) (2*u) =
      boundedDurationRatio N u ^ 2 := by
  have hs : 0 < Real.sin u := Real.sin_pos_of_pos_of_lt_pi hu (by linarith [Real.pi_pos])
  have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have he := triangularCosineNumerator_identity (2*u) N
  have hleft := Real.cos_two_mul_eq_one_sub u
  have hright := Real.cos_two_mul u
  have hn := Real.cos_two_mul_eq_one_sub ((N : ℝ)*u)
  rw [show 2*((N : ℝ)*u) = (N : ℝ)*(2*u) by ring] at hn
  have hnum : triangularCosineNumerator (2*u) N =
      Real.cos u ^ 2 * Real.sin ((N : ℝ)*u)^2 / Real.sin u^2 := by
    apply (eq_div_iff (sq_pos_of_pos hs).ne').mpr
    rw [hn] at he
    have hc : 1 + Real.cos (2*u) = 2 * Real.cos u^2 := by linarith only [hright]
    have hs₂ : 2 * (1 - Real.cos (2*u)) = 4 * Real.sin u^2 := by linarith only [hleft]
    rw [hc, hs₂] at he
    nlinarith only [he]
  rw [triangularCount_cosine_numerator hh hN, hnum]
  unfold boundedDurationRatio
  field_simp [hN'.ne', hs.ne']

/-- The uniform law on [0, N h] contributes cos(Nu) times B_N at
frequency 2u. This identity is used for the even case of the half-duration law. -/
theorem uniformCount_cosine_ratio {h : ℝ} (hh : 0 < h) {N : ℕ} (hN : 0 < N)
    {u : ℝ} (hu : 0 < u) (huπ : u < Real.pi/2) :
    cosineSeries (countLawWeight (roundedDurationLaw h (uniformDurationLaw ((N : ℝ)*h)))) (2*u) =
      Real.cos ((N : ℝ)*u) * boundedDurationRatio N u := by
  have hs : 0 < Real.sin u := Real.sin_pos_of_pos_of_lt_pi hu (by linarith [Real.pi_pos])
  have hc : 0 < Real.cos u :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], huπ⟩
  have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have he := uniformCosine_sum_identity (2*u) N
  have hn := Real.sin_two_mul ((N : ℝ)*u)
  rw [show 2*((N : ℝ)*u) = (N : ℝ)*(2*u) by ring] at hn
  rw [Real.sin_two_mul u, Real.cos_two_mul u, hn] at he
  have hnum : (∑ j ∈ Finset.range N, cellCosine (2*u) j) =
      (Real.cos u * Real.sin ((N : ℝ)*u) * Real.cos ((N : ℝ)*u)) / Real.sin u := by
    apply (eq_div_iff hs.ne').mpr
    apply mul_left_cancel₀ (show (4 : ℝ) * Real.cos u ≠ 0 by positivity)
    nlinarith only [he]
  rw [uniformCount_cosine_numerator hh hN, hnum]
  unfold boundedDurationRatio
  field_simp [hN'.ne', hs.ne']

theorem uniformDuration_Ico {T a b : ℝ} (hT : 0 < T) (ha : 0 ≤ a) :
    uniformDurationLaw T (Ico a b) = ENNReal.ofReal ((min b T - a)/T) := by
  rw [uniformDurationLaw, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply measurableSet_Ico, Set.Ico_inter_Ico, sup_of_le_left ha,
    Real.volume_Ico, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [one_div, inv_mul_eq_div]

/-- Appendix C, even N: the uniform law on [0, N h/2] has coefficient B_N. -/
theorem uniformHalfCount_cosine_ratio_even {h : ℝ} (hh : 0 < h) {K : ℕ} (hK : 0 < K)
    {u : ℝ} (hu : 0 < u) (huπ : u < Real.pi/2) :
    cosineSeries (countLawWeight
      (roundedDurationLaw h (uniformDurationLaw (((2*K : ℕ) : ℝ)*h/2)))) (2*u) =
      boundedDurationRatio (2*K) u := by
  have hs : 0 < Real.sin u := Real.sin_pos_of_pos_of_lt_pi hu (by linarith [Real.pi_pos])
  have hK' : (0 : ℝ) < K := Nat.cast_pos.mpr hK
  have hT : ((2*K : ℕ) : ℝ)*h/2 = (K : ℝ)*h := by push_cast; ring
  have h2 : Real.sin (((2*K : ℕ) : ℝ)*u) =
      2 * Real.sin ((K : ℝ)*u) * Real.cos ((K : ℝ)*u) := by
    rw [show ((2*K : ℕ) : ℝ)*u = 2*((K : ℝ)*u) by push_cast; ring, Real.sin_two_mul]
  rw [hT, uniformCount_cosine_ratio hh hK hu huπ]
  unfold boundedDurationRatio
  rw [h2]
  push_cast
  field_simp [hK'.ne', hs.ne']

/-- Appendix C, odd N: the uniform law on [0, N h/2] has coefficient cos u * B_N. -/
theorem uniformHalfCount_cosine_ratio_odd {h : ℝ} (hh : 0 < h) (K : ℕ)
    {u : ℝ} (hu : 0 < u) (huπ : u < Real.pi/2) :
    cosineSeries (countLawWeight
      (roundedDurationLaw h (uniformDurationLaw (((2*K+1 : ℕ) : ℝ)*h/2)))) (2*u) =
      Real.cos u * boundedDurationRatio (2*K+1) u := by
  have hs : 0 < Real.sin u := Real.sin_pos_of_pos_of_lt_pi hu (by linarith [Real.pi_pos])
  have hc : 0 < Real.cos u := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], huπ⟩
  set Nr : ℝ := ((2*K+1 : ℕ) : ℝ) with hNr
  have hNval : Nr = 2*(K : ℝ)+1 := by rw [hNr]; push_cast; ring
  have hNpos : 0 < Nr := by rw [hNval]; positivity
  set T : ℝ := Nr*h/2 with hTdef
  have hT : 0 < T := by positivity
  have hKT : (K : ℝ)*h < T := by rw [hTdef, hNval]; nlinarith
  have hTK : T < ((K+1 : ℕ) : ℝ)*h := by rw [hTdef, hNval]; push_cast; nlinarith
  have : IsProbabilityMeasure (uniformDurationLaw T) := uniformDuration_probability hT
  have hsupp : ∀ᵐ τ ∂uniformDurationLaw T, 0 ≤ τ ∧ τ < ((K+1 : ℕ) : ℝ)*h :=
    uniformDuration_ae.mono fun _ ht => ⟨ht.1, ht.2.trans hTK⟩
  have hlast : (uniformDurationLaw T (Ico ((K : ℝ)*h) (((K : ℝ)+1)*h))).toReal = 1/Nr := by
    rw [uniformDuration_Ico hT (by positivity),
      min_eq_right (by push_cast at hTK; linarith),
      ENNReal.toReal_ofReal (div_nonneg (by linarith) hT.le), hTdef, hNval]
    field_simp
    ring
  have hcell : ∀ j ∈ Finset.range K,
      (uniformDurationLaw T (Ico ((j : ℝ)*h) (((j : ℝ)+1)*h))).toReal * cellCosine (2*u) j =
        2/Nr * cellCosine (2*u) j := by
    intro j hj
    have hjK : (j : ℝ)+1 ≤ K := by exact_mod_cast Finset.mem_range.mp hj
    have hle : ((j : ℝ)+1)*h ≤ T := (mul_le_mul_of_nonneg_right hjK hh.le).trans hKT.le
    have hmass : (min (((j : ℝ)+1)*h) T - (j : ℝ)*h)/T = 2/Nr := by
      rw [min_eq_left hle, hTdef]
      field_simp
      ring
    rw [uniformDuration_Ico hT (by positivity), hmass,
      ENNReal.toReal_ofReal (by positivity)]
  rw [roundedDuration_cosine_cells h hh (K+1) _ hsupp, Finset.sum_range_succ,
    Finset.sum_congr rfl hcell, ← Finset.mul_sum, hlast]
  set S := ∑ j ∈ Finset.range K, cellCosine (2*u) j with hSdef
  set a : ℝ := (K : ℝ)*(2*u) with ha
  have he := uniformCosine_sum_identity (2*u) K
  rw [Real.sin_two_mul u, Real.cos_two_mul u] at he
  have hS : S * (2*Real.sin u) = Real.cos u * Real.sin a := by
    apply mul_left_cancel₀ (show (2 : ℝ) * Real.cos u ≠ 0 by positivity)
    linear_combination he
  have hNu : Nr*u = a + u := by rw [hNval, ha]; ring
  have hcellK : cellCosine (2*u) K = (Real.cos a + Real.cos (a + 2*u))/2 := by
    unfold cellCosine
    rw [show ((K : ℝ)+1)*(2*u) = a + 2*u by rw [ha]; ring]
  have key : (2*S + cellCosine (2*u) K) * Real.sin u =
      Real.cos u * (Real.cos u * Real.sin (Nr*u)) := by
    rw [hcellK, hNu, Real.cos_add a (2*u), Real.sin_add a u, Real.sin_two_mul u,
      Real.cos_two_mul u]
    linear_combination hS - Real.cos u * Real.sin a * Real.sin_sq_add_cos_sq u
  have hval : 2*S + cellCosine (2*u) K =
      Real.cos u * (Real.cos u * Real.sin (Nr*u)) / Real.sin u :=
    (eq_div_iff hs.ne').mpr key
  unfold boundedDurationRatio
  calc 2/Nr * S + 1/Nr * cellCosine (2*u) K
      = (2*S + cellCosine (2*u) K)/Nr := by ring
    _ = _ := by
      rw [hval, ← hNr]
      field_simp

/-- Appendix C: the printed formula for the uniform law on [0, N h/2]. -/
theorem uniformHalfCount_cosine_ratio {h : ℝ} (hh : 0 < h) {N : ℕ} (hN : 0 < N)
    {u : ℝ} (hu : 0 < u) (huπ : u < Real.pi/2) :
    cosineSeries (countLawWeight
      (roundedDurationLaw h (uniformDurationLaw ((N : ℝ)*h/2)))) (2*u) =
      (if Even N then 1 else Real.cos u) * boundedDurationRatio N u := by
  rcases Nat.even_or_odd' N with ⟨K, rfl | rfl⟩
  · rw [ite_eq_left (even_two_mul K), one_mul]
    exact uniformHalfCount_cosine_ratio_even hh (by omega) hu huπ
  · rw [ite_eq_right (Nat.not_even_iff_odd.mpr (odd_two_mul_add_one K))]
    exact uniformHalfCount_cosine_ratio_odd hh K hu huπ

end BreakingResonance

#print axioms BreakingResonance.triangularCount_cosine_numerator
#print axioms BreakingResonance.uniformCount_cosine_numerator
#print axioms BreakingResonance.triangularCount_cosine_ratio
#print axioms BreakingResonance.uniformCount_cosine_ratio
#print axioms BreakingResonance.uniformDuration_Ico
#print axioms BreakingResonance.uniformHalfCount_cosine_ratio_even
#print axioms BreakingResonance.uniformHalfCount_cosine_ratio_odd
#print axioms BreakingResonance.uniformHalfCount_cosine_ratio
