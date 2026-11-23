import BreakingResonance.ExponentialCountLaw

/-! Conditioning the exponential duration at a cell boundary. -/
noncomputable section
namespace BreakingResonance
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

theorem exponentialDuration_cutoff_mass {s h : ℝ} (hs : 0 < s) (hh : 0 < h) (M : ℕ) :
    (expMeasure s).real (Iic ((M : ℝ)*h)) = 1-(Real.exp (-(s*h)))^M := by
  rw [exponentialDuration_Iic hs (by positivity),
    show -(s*((M : ℝ)*h)) = (M : ℝ)*(-(s*h)) by ring, Real.exp_nat_mul]

theorem exponentialDuration_conditional_cell_mass {s h : ℝ} (hs : 0 < s) (hh : 0 < h)
    {M j : ℕ} (hj : j < M) :
    let r := Real.exp (-(s*h))
    (conditionalDurationLaw (expMeasure s) ((M : ℝ)*h)).real
      (Ico ((j : ℝ)*h) (((j : ℝ)+1)*h)) = (1-r)*r^j / (1-r^M) := by
  dsimp only
  let ρ := expMeasure s
  let T := (M : ℝ)*h
  have hM : (j : ℝ)+1 ≤ M := by exact_mod_cast hj
  have hsub : Ico ((j : ℝ)*h) (((j : ℝ)+1)*h) ⊆ Iic T :=
    fun _ hx => hx.2.le.trans (mul_le_mul_of_nonneg_right hM hh.le)
  rw [conditionalDurationLaw, Measure.real, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_eq_self _ hsub, ENNReal.toReal_mul, ENNReal.toReal_inv]
  change ((ρ.real (Iic T))⁻¹) * (ρ.real (Ico ((j : ℝ)*h) (((j : ℝ)+1)*h))) = _
  have hcell := exponentialDuration_floorMass hs hh j
  change (((expMeasure s).map (fun τ => Nat.floor (τ/h))) {j}).toReal = _ at hcell
  rw [floorDuration_map_apply_singleton h hh
    ((exponentialDuration_positive hs).mono fun _ ht => ht.le)] at hcell
  rw [exponentialDuration_cutoff_mass hs hh, show
    ρ.real (Ico ((j : ℝ)*h) (((j : ℝ)+1)*h)) = _ from hcell]
  rw [div_eq_mul_inv, mul_comm]

theorem exponentialDuration_conditional_support {s h : ℝ} (hs : 0 < s) (M : ℕ) :
    ∀ᵐ τ ∂conditionalDurationLaw (expMeasure s) ((M : ℝ)*h), 0 ≤ τ ∧ τ < (M : ℝ)*h := by
  let ρ := expMeasure s
  let T := (M : ℝ)*h
  let : NullSingletonClass ρ := by unfold ρ expMeasure gammaMeasure; infer_instance
  have hI : ρ.restrict (Iic T) = ρ.restrict (Iio T) :=
    (Measure.restrict_congr_set Iio_ae_eq_Iic).symm
  unfold conditionalDurationLaw
  change ∀ᵐ τ ∂(ρ (Iic T))⁻¹ • ρ.restrict (Iic T), 0 ≤ τ ∧ τ < T
  rw [hI]
  have hn : ∀ᵐ τ ∂ρ.restrict (Iio T), 0 ≤ τ :=
    ae_mono Measure.restrict_le_self ((exponentialDuration_positive hs).mono fun _ hx => hx.le)
  exact Measure.ae_smul_measure (hn.and (ae_restrict_mem measurableSet_Iio)) _

theorem exponentialDuration_conditional_probability {s h : ℝ} (hs : 0 < s) (hh : 0 < h)
    {M : ℕ} (hM : 0 < M) :
    IsProbabilityMeasure (conditionalDurationLaw (expMeasure s) ((M : ℝ)*h)) := by
  let : IsProbabilityMeasure (expMeasure s) := isProbabilityMeasure_expMeasure hs
  have hT : 0 < (M : ℝ)*h := mul_pos (Nat.cast_pos.mpr hM) hh
  have hpos : 0 < (expMeasure s).real (Iic ((M : ℝ)*h)) := by
    rw [exponentialDuration_Iic hs hT.le]
    exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr (mul_pos hs hT)))
  apply conditionalDuration_isProbability
  intro hn
  simp only [Measure.real, hn, ENNReal.toReal_zero] at hpos
  exact (lt_irrefl 0) hpos

/-- Conditioning on M cells multiplies the full characteristic function
by the normalized finite geometric-series factor. -/
theorem exponentialDuration_conditional_characteristic {s h : ℝ} (hs : 0 < s) (hh : 0 < h)
    {M : ℕ} (hM : 0 < M) (θ : ℝ) :
    let r := Real.exp (-(s*h))
    let z := Complex.exp ((θ : ℂ)*Complex.I)
    (∫ j : ℕ, Complex.exp ((((j : ℝ)*θ : ℝ) : ℂ)*Complex.I)
        ∂roundedDurationLaw h (conditionalDurationLaw (expMeasure s) ((M : ℝ)*h))) =
      (∫ j : ℕ, Complex.exp ((((j : ℝ)*θ : ℝ) : ℂ)*Complex.I)
        ∂roundedDurationLaw h (expMeasure s)) *
      ((1-((r : ℂ)*z)^M)/(1-(r : ℂ)^M)) := by
  dsimp only
  let r := Real.exp (-(s*h))
  let z := Complex.exp ((θ : ℂ)*Complex.I)
  let ν := conditionalDurationLaw (expMeasure s) ((M : ℝ)*h)
  let : IsProbabilityMeasure ν := exponentialDuration_conditional_probability hs hh hM
  let f (j : ℕ) := Complex.exp ((((j : ℝ)*θ : ℝ) : ℂ)*Complex.I)
  let w (j : ℕ) := (1/2 : ℝ≥0∞) * ν (Ico ((j : ℝ)*h) (((j : ℝ)+1)*h))
  have hw (j : ℕ) : w j ≠ ∞ := ENNReal.mul_ne_top (by norm_num) (measure_ne_top _ _)
  have hi (j b : ℕ) : Integrable f (w j • Measure.dirac (j+b)) :=
    (integrable_dirac (by simp)).smul_measure (hw j)
  have hpow (j : ℕ) : f j = z^j := by
    dsimp only [f,z]
    rw [← Complex.exp_nat_mul]
    push_cast
    ring_nf
  have hr : 0 < r := Real.exp_pos _
  have hr₁ : r < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr (mul_pos hs hh))
  have hnorm : ‖(r : ℂ)*z‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr.le,
      show ‖z‖ = 1 from Complex.norm_exp_ofReal_mul_I θ, mul_one]
    exact hr₁
  have hdiff : 1-(r : ℂ)*z ≠ 0 := by
    intro he
    have hx : (r : ℂ)*z = 1 := by linear_combination -he
    rw [hx, norm_one] at hnorm
    exact (lt_irrefl 1) hnorm
  have hret : 1-(r : ℂ)^M ≠ 0 := by
    exact_mod_cast (sub_ne_zero.mpr (ne_of_gt (pow_lt_one₀ hr.le hr₁ hM.ne')) : 1-r^M ≠ 0)
  change (∫ j, f j ∂roundedDurationLaw h ν) = _
  rw [exponentialDuration_rounded_characteristic hs hh,
    roundedDuration_eq_cell_sum h hh M ν (exponentialDuration_conditional_support hs M),
    integral_finsetSum_measure (fun j _ => integrable_finsetSum_measure.2 (fun b _ => hi j b))]
  have he : (∑ j ∈ Finset.range M,
      ∫ a, f a ∂(∑ b ∈ Finset.range 2, w j • Measure.dirac (j+b))) =
      ((1+z)*(1-(r : ℂ))/(2*(1-(r : ℂ)^M))) *
        (∑ j ∈ Finset.range M, (((r : ℂ)*z)^j)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [integral_finsetSum_measure (fun b _ => hi j b)]
    simp only [integral_smul_measure, integral_dirac, Finset.sum_range_succ,
      Finset.sum_range_zero, Nat.add_zero, zero_add, hpow, pow_succ, RCLike.real_smul_eq_coe_mul]
    have hmass : (w j).toReal = (1/2)*((1-r)*r^j/(1-r^M)) := by
      have hh' := exponentialDuration_conditional_cell_mass hs hh (Finset.mem_range.mp hj)
      change (ν (Ico ((j : ℝ)*h) (((j : ℝ)+1)*h))).toReal = (1-r)*r^j/(1-r^M) at hh'
      simp only [w, ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_one,
        ENNReal.toReal_ofNat, hh']
    have hcast : ((w j).toReal : ℂ) = (1/2)*((1-(r : ℂ))*(r : ℂ)^j/(1-(r : ℂ)^M)) := by
      rw [hmass]
      simp only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_pow,
        Complex.ofReal_one, Complex.ofReal_ofNat]
    change ((w j).toReal : ℂ) * z^j + ((w j).toReal : ℂ) * (z^j*z) = _
    rw [hcast]
    rw [mul_pow]
    field_simp [hret]
  change (∑ j ∈ Finset.range M,
      ∫ a, f a ∂(∑ b ∈ Finset.range 2, w j • Measure.dirac (j+b))) =
    (((1+z)*(1-(r : ℂ)))/(2*(1-(r : ℂ)*z))) * ((1-((r : ℂ)*z)^M)/(1-(r : ℂ)^M))
  rw [he, geom_sum_eq (sub_ne_zero.mp hdiff |>.symm)]
  rw [show (r : ℂ)*z-1 = -(1-(r : ℂ)*z) by ring,
    show ((r : ℂ)*z)^M-1 = -(1-((r : ℂ)*z)^M) by ring,
    neg_div_neg_eq]
  field_simp [hret, hdiff]

end BreakingResonance

#print axioms BreakingResonance.exponentialDuration_conditional_characteristic
