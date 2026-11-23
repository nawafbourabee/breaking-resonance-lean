import BreakingResonance.ConditionalFourierLow
import BreakingResonance.TriangularReferenceLaw

/-! Lemma 5.3 with the explicit cutoff, comparison and spectral constants. -/
noncomputable section
namespace BreakingResonance
open MeasureTheory Set

/-- The least even integer at least twice a positive threshold. -/
def evenHarmonic (x : ℝ) : ℕ := 2 * Nat.ceil x

theorem evenHarmonic_even (x : ℝ) : Even (evenHarmonic x) := even_two_mul _

theorem evenHarmonic_le {x : ℝ} : 2*x ≤ (evenHarmonic x : ℝ) := by
  unfold evenHarmonic
  push_cast
  exact mul_le_mul_of_nonneg_left (Nat.le_ceil x) (by norm_num)

theorem evenHarmonic_pos {x : ℝ} (hx : 0 < x) : 0 < evenHarmonic x := by
  exact Nat.cast_pos.mp ((mul_pos (by norm_num : (0 : ℝ) < 2) hx).trans_le evenHarmonic_le)

theorem evenHarmonic_divisor_bounds {x δ a : ℝ}
    (hx : 0 < x) (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (ha : 1 ≤ a) :
    0 < δ/(a*(evenHarmonic x : ℝ)^2) ∧ δ/(a*(evenHarmonic x : ℝ)^2) ≤ 1 := by
  have hk : 0 < evenHarmonic x := evenHarmonic_pos hx
  have hk₁ : (1 : ℝ) ≤ evenHarmonic x := by exact_mod_cast hk
  have hk₂ : (1 : ℝ) ≤ (evenHarmonic x : ℝ)^2 := by
    simpa only [one_pow] using
      (sq_le_sq₀ zero_le_one (Nat.cast_nonneg (evenHarmonic x))).mpr hk₁
  have hd : 0 < a*(evenHarmonic x : ℝ)^2 := by positivity
  exact ⟨div_pos hδ hd, (div_le_one hd).mpr
    (hδ₁.trans (by nlinarith only [mul_le_mul_of_nonneg_left hk₂ (by linarith : 0 ≤ a), ha]))⟩

theorem evenHarmonic_frequency_lower {x h s θ : ℝ} (hh : 0 < h) (hx : 0 < x)
    (hf : h*s/x ≤ |θ|) :
    2*s ≤ (evenHarmonic x : ℝ) * (|θ|/h) := by
  have hv : h*s ≤ |θ| * x := (div_le_iff₀ hx).mp hf
  have hkx : 2*x ≤ (evenHarmonic x : ℝ) := evenHarmonic_le
  rw [← mul_div_assoc]
  apply (le_div_iff₀ hh).mpr
  calc
    (2*s)*h = 2*(h*s) := by ring
    _ ≤ 2*(|θ| * x) := by linarith only [hv]
    _ = (2*x)*|θ| := by ring
    _ ≤ (evenHarmonic x : ℝ)*|θ| := mul_le_mul_of_nonneg_right hkx (abs_nonneg θ)

/-- The gap from the independent Bernoulli variable is positive and fits
within the intermediate-frequency and low-frequency estimates. -/
theorem bernoulli_gap_bounds {ζ : ℝ} (hζ : 0 < ζ) (hζ₁ : ζ ≤ 1) :
    0 < 1 - Real.cos (ζ/2) ∧ 1 - Real.cos (ζ/2) ≤ ζ := by
  have hf := Real.strictAntiOn_cos (show (0 : ℝ) ∈ Icc (0 : ℝ) Real.pi from
    ⟨le_rfl, Real.pi_pos.le⟩) (show ζ/2 ∈ Icc (0 : ℝ) Real.pi from
    ⟨by positivity, by linarith [Real.pi_gt_three]⟩) (show 0 < ζ/2 by positivity)
  rw [Real.cos_zero] at hf
  have hl := Real.abs_cos_sub_cos_le (ζ/2) 0
  rw [Real.cos_zero, sub_zero, abs_of_pos (show 0 < ζ/2 by positivity)] at hl
  exact ⟨sub_pos.mpr hf, by linarith only [(abs_le.mp hl).1, hζ]⟩

theorem nonresonantDuration_one_sub_cos_lower (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    {m b δ : ℝ} (hρ : NonresonantDuration ρ m b δ) (ω : ℝ) (hω : 2*Real.sqrt m ≤ ω) :
    δ ≤ ∫ τ : ℝ, 1 - Real.cos (ω*τ) ∂ρ := by
  rw [integral_sub (integrable_const _) (integrable_duration_cos ρ ω)]
  simp only [integral_const, probReal_univ, one_smul]
  linarith only [hρ.cosine_le ω hω]

/-- The conditional characteristic function has a gap at low, intermediate,
and high frequencies. Here k, ζ, and c₀ are exactly those of Lemma 5.3. -/
theorem roundedDuration_conditional_gap (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    {m b δ : ℝ} (hρ : NonresonantDuration ρ m b δ) (τstar : ℝ) (hcut : 0 < τstar)
    (htail : (ρ (Ioi τstar)).toReal ≤ δ/4)
    (h : ℝ) (hh : 0 < h) (hhm : h^2*m ≤ δ/16) (θ : ℝ) (hθ : |θ| ≤ Real.pi) :
    let k := evenHarmonic (Real.sqrt m*τstar + 1)
    let ζ := δ/(4*(k : ℝ)^2)
    let c₀ := min (δ/64) (min ζ (1 - Real.cos (ζ/2)))
    c₀ * min (θ^2/(h^2*m)) 1 ≤
      1 - cosineSeries (countLawWeight (roundedDurationLaw h (conditionalDurationLaw ρ τstar))) θ := by
  dsimp only
  set x := Real.sqrt m*τstar + 1
  set k := evenHarmonic x
  set ζ := δ/(4*(k : ℝ)^2)
  set c₀ := min (δ/64) (min ζ (1 - Real.cos (ζ/2)))
  let ν := conditionalDurationLaw ρ τstar
  let : IsProbabilityMeasure ν :=
    conditionalDuration_isProbability ρ τstar (retainedDuration_ne_zero ρ τstar hρ.gap_le_one htail)
  have hν : ∀ᵐ τ ∂ν, 0 ≤ τ :=
    (conditionalDuration_positive_bounded ρ τstar hρ.positive_ae).mono fun _ ht => ht.1.le
  have hx : 0 < x := by dsimp [x]; positivity
  have hk : 0 < k := evenHarmonic_pos hx
  have ⟨hζ, hζ₁⟩ : 0 < ζ ∧ ζ ≤ 1 :=
    evenHarmonic_divisor_bounds hx hρ.gap_pos hρ.gap_le_one (by norm_num)
  have hg := bernoulli_gap_bounds hζ hζ₁
  have hc : 0 ≤ c₀ := le_min (by linarith only [hρ.gap_pos]) (le_min hζ.le hg.1.le)
  have hcζ : c₀ ≤ ζ := (min_le_right _ _).trans (min_le_left _ _)
  have hccos : c₀ ≤ 1 - Real.cos (ζ/2) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have ht_nonneg : 0 ≤ θ^2/(h^2*m) :=
    div_nonneg (sq_nonneg θ) (mul_nonneg (sq_nonneg h) hρ.m_pos.le)
  by_cases hl : |θ| ≤ h*Real.sqrt m/x
  · exact (mul_le_mul (min_le_left (δ/64) _) (min_le_left _ _) (le_min ht_nonneg zero_le_one)
      (by linarith only [hρ.gap_pos])).trans
      (roundedDuration_conditional_low ρ hρ τstar hcut htail h hh hhm θ hl).1
  · have hprod : 2 * Real.sqrt m ≤ (k : ℝ) * (|θ|/h) :=
      evenHarmonic_frequency_lower hh hx (le_of_not_ge hl)
    by_cases hm : |θ| ≤ ζ
    · have hscale : (δ/2)/(2*(k : ℝ)^2) = ζ := by dsimp only [ζ]; rw [div_div]; ring
      have hi := (roundedDuration_intermediate_gap h hh ν hν k (evenHarmonic_even x)
        hk (δ/2) θ (hscale.symm ▸ hm)
        (conditionalDuration_one_sub_cos_lower ρ hρ τstar htail _ hprod)).1
      rw [hscale] at hi
      exact (mul_le_of_le_one_right hc (min_le_right _ _)).trans (hcζ.trans hi)
    · have hi := roundedDuration_abs_cosineSeries_high h ν hζ.le (le_of_not_ge hm) hθ
      have hlow := (le_abs_self _).trans hi
      exact (mul_le_of_le_one_right hc (min_le_right _ _)).trans
        (hccos.trans (by linarith only [hlow]))

/-- The lower spectral gap uses the full count law. This is the second
bound in (3.1), with β_P as given in Lemma 5.3. -/
theorem roundedDuration_full_gap (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    {m b δ : ℝ} (hρ : NonresonantDuration ρ m b δ)
    (h : ℝ) (hh : 0 < h) (hhm : h^2*m ≤ δ/16) (θ : ℝ) (hθ : |θ| ≤ Real.pi) :
    let kρ := evenHarmonic (2*(b+1))
    let ζρ := δ/(2*(kρ : ℝ)^2)
    1 - Real.cos (ζρ/2) ≤
      1 + cosineSeries (countLawWeight (roundedDurationLaw h ρ)) θ := by
  dsimp only
  set x := 2*(b+1)
  set kρ := evenHarmonic x
  set ζρ := δ/(2*(kρ : ℝ)^2)
  have hx : 0 < x := by dsimp [x]; linarith only [hρ.b_pos]
  have hk : 0 < kρ := evenHarmonic_pos hx
  have ⟨hζ, hζ₁⟩ : 0 < ζρ ∧ ζρ ≤ 1 :=
    evenHarmonic_divisor_bounds hx hρ.gap_pos hρ.gap_le_one (by norm_num)
  have hg := bernoulli_gap_bounds hζ hζ₁
  have hs : 0 < Real.sqrt m := Real.sqrt_pos.2 hρ.m_pos
  have hr : h*Real.sqrt m ≤ 1 := by
    apply (sq_le_sq₀ (mul_nonneg hh.le hs.le) zero_le_one).mp
    rw [mul_pow, Real.sq_sqrt hρ.m_pos.le]
    linarith only [hhm, hρ.gap_le_one]
  by_cases hl : |θ| ≤ h*Real.sqrt m/x
  · have hlow := roundedDuration_full_low h hh ρ hρ hr θ hl
    linarith only [hg.2, hζ₁, hlow]
  · by_cases hm : |θ| ≤ ζρ
    · have hprod : 2*Real.sqrt m ≤ (kρ : ℝ)*(|θ|/h) :=
        evenHarmonic_frequency_lower hh hx (le_of_not_ge hl)
      exact hg.2.trans (roundedDuration_intermediate_gap h hh ρ
        (hρ.positive_ae.mono fun _ ht => ht.le) kρ (evenHarmonic_even x) hk δ θ hm
        (nonresonantDuration_one_sub_cos_lower ρ hρ _ hprod)).2
    · have hhigh := roundedDuration_abs_cosineSeries_high h ρ hζ.le (le_of_not_ge hm) hθ
      have hlower := (neg_le_neg hhigh).trans (neg_abs_le _)
      linarith only [hlower]

/-- Lemma 5.3: both bounds in (3.1) for the actual rounded count laws,
with c = c₀/8 and β_P = 1 - cos(ζρ/2). -/
theorem roundedFourierBounds (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    {m b δ : ℝ} (hρ : NonresonantDuration ρ m b δ)
    (τstar : ℝ) (hcut : 0 < τstar) (htail : (ρ (Ioi τstar)).toReal ≤ δ/4)
    (N : ℕ) (hN : 0 < N) (h : ℝ) (hh : h = 4/((N : ℝ)*Real.sqrt m))
    (hhm : h^2*m ≤ δ/16) :
    let k := evenHarmonic (Real.sqrt m*τstar + 1)
    let ζ := δ/(4*(k : ℝ)^2)
    let c₀ := min (δ/64) (min ζ (1 - Real.cos (ζ/2)))
    let c := c₀/8
    let kρ := evenHarmonic (2*(b+1))
    let ζρ := δ/(2*(kρ : ℝ)^2)
    let β := 1 - Real.cos (ζρ/2)
    let w := roundedDurationLaw h (conditionalDurationLaw ρ τstar)
    let q := triangularCountLaw h N
    let μJ := roundedDurationLaw h ρ
    (0 < c ∧ c ≤ 1) ∧ (0 < β ∧ β ≤ 1) ∧
      ∀ θ ∈ Icc (-Real.pi) Real.pi,
        c * (1 - cosineSeries (countLawWeight q) θ) ≤
          1 - cosineSeries (countLawWeight w) θ ∧
        β ≤ 1 + cosineSeries (countLawWeight μJ) θ := by
  dsimp only
  set x := Real.sqrt m*τstar + 1
  set k := evenHarmonic x
  set ζ := δ/(4*(k : ℝ)^2)
  set c₀ := min (δ/64) (min ζ (1 - Real.cos (ζ/2)))
  set xρ := 2*(b+1)
  set kρ := evenHarmonic xρ
  set ζρ := δ/(2*(kρ : ℝ)^2)
  have hx : 0 < x := by dsimp [x]; positivity
  have hxρ : 0 < xρ := by dsimp [xρ]; linarith only [hρ.b_pos]
  have ⟨hζ, hζ₁⟩ : 0 < ζ ∧ ζ ≤ 1 :=
    evenHarmonic_divisor_bounds hx hρ.gap_pos hρ.gap_le_one (by norm_num)
  have ⟨hζρ, hζρ₁⟩ : 0 < ζρ ∧ ζρ ≤ 1 :=
    evenHarmonic_divisor_bounds hxρ hρ.gap_pos hρ.gap_le_one (by norm_num)
  have hc₀ : 0 < c₀ :=
    lt_min (by linarith only [hρ.gap_pos]) (lt_min hζ (bernoulli_gap_bounds hζ hζ₁).1)
  refine ⟨⟨by positivity, ?_⟩,
    ⟨(bernoulli_gap_bounds hζρ hζρ₁).1, (bernoulli_gap_bounds hζρ hζρ₁).2.trans hζρ₁⟩, ?_⟩
  · have hc₁ : c₀ ≤ δ/64 := min_le_left _ _
    linarith only [hc₁, hρ.gap_le_one]
  intro θ hθ
  have hπ : |θ| ≤ Real.pi := abs_le.mpr hθ
  have hs : 0 < Real.sqrt m := Real.sqrt_pos.mpr hρ.m_pos
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hhp : 0 < h := hh.symm ▸ div_pos (by norm_num) (mul_pos hNr hs)
  refine ⟨?_, roundedDuration_full_gap ρ hρ h hhp hhm θ hπ⟩
  let : IsProbabilityMeasure (triangularCountLaw h N) := triangularCount_probability hhp hN
  have hlo := roundedDuration_conditional_gap ρ hρ τstar hcut htail h hhp hhm θ hπ
  have hq := cosineSeries_gap_upper_of_count_le (triangularCountLaw h N) N
    (triangularCount_ae_le hhp N) θ
  have hhN : (N : ℝ)*h*Real.sqrt m = 4 := by
    rw [hh]
    field_simp [hNr.ne', hs.ne']
  have hden : 0 < h^2*m := mul_pos (sq_pos_of_pos hhp) hρ.m_pos
  have hsquare : (N : ℝ)^2 * (h^2*m) = 16 := by
    have he := congrArg (fun t : ℝ => t^2) hhN
    rw [mul_pow, mul_pow, Real.sq_sqrt hρ.m_pos.le] at he
    nlinarith only [he]
  have he : (N : ℝ)^2*θ^2/2 = 8*(θ^2/(h^2*m)) := by
    rw [← mul_div_assoc]
    apply (eq_div_iff hden.ne').mpr
    nlinarith only [congrArg (fun t : ℝ => t * θ^2) hsquare]
  rw [he] at hq
  let y := θ^2/(h^2*m)
  have hq' : 1 - cosineSeries (countLawWeight (triangularCountLaw h N)) θ ≤ 8 * min y 1 := by
    by_cases hy : y ≤ 1
    · rw [min_eq_left hy]
      exact hq.trans (min_le_left _ _)
    · rw [min_eq_right (le_of_not_ge hy)]
      exact hq.trans ((min_le_right _ _).trans (by norm_num))
  calc
    _ ≤ (c₀/8) * (8 * min y 1) := mul_le_mul_of_nonneg_left hq' (by positivity)
    _ = c₀ * min y 1 := by ring
    _ ≤ _ := hlo

end BreakingResonance

#print axioms BreakingResonance.roundedDuration_conditional_gap
#print axioms BreakingResonance.roundedDuration_full_gap
#print axioms BreakingResonance.roundedFourierBounds
