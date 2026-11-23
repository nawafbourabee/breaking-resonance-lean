import BreakingResonance.RoundingCost

/-! Arithmetic and expected-duration steps at the end of Theorem 2.
The expanding orbit and the acceptance estimate for its target are separate,
unformalized dependencies. No theorem here assumes the main lower bound. -/
namespace BreakingResonance
noncomputable section
open MeasureTheory

theorem initial_bad_mass_margin (κ : ℝ) (hκ : 64 ≤ κ) :
    4 / κ ^ 4 ≤ 1/20 := by
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 64) hκ 4
  apply (div_le_iff₀ (by positivity : 0 < κ ^ 4)).mpr
  norm_num at hp
  linarith

theorem roundedDuration_mean_lower (κ h : ℝ) (hκ : 64 ≤ κ)
    (hh : 0 < h) (hh1 : h ≤ 1) (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    (hτ : Integrable (fun τ : ℝ => τ) ρ) (hpos : ∀ᵐ τ ∂ρ, 0 ≤ τ)
    (hmean : 2 * Real.sqrt κ / 3 ≤ ∫ τ : ℝ, τ ∂ρ) :
    Real.sqrt κ / (2*h) ≤ ∫ j : ℕ, (j : ℝ) ∂roundedDurationLaw h ρ := by
  have hround := (roundedDuration_mean_bounds h hh ρ hτ hpos).1
  have hs : 8 ≤ Real.sqrt κ := by
    nlinarith [Real.sq_sqrt (by linarith : 0 ≤ κ), Real.sqrt_nonneg κ]
  have hm := (div_le_div_of_nonneg_right hmean hh.le)
  have htimes := mul_le_mul_of_nonneg_right hround hh.le
  have hdiv : ((∫ τ : ℝ, τ ∂ρ)/h - 1/2)*h =
      (∫ τ : ℝ, τ ∂ρ) - h/2 := by field_simp
  rw [hdiv] at htimes
  apply (div_le_iff₀ (by positivity : 0 < 2*h)).mpr
  nlinarith

theorem weighted_cost_lower (C c₁ c₂ p κ Λ : ℝ)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hp : 0 < p) (hκ : 0 < κ) (hΛ : 0 < Λ)
    (hfirst : c₁ * p * Real.sqrt κ ≤ C)
    (hsecond : c₂ * κ / (p ^ 2 * Λ) ≤ C) :
    c₁ ^ (2/3 : ℝ) * c₂ ^ (1/3 : ℝ) * κ ^ (2/3 : ℝ) /
      Λ ^ (1/3 : ℝ) ≤ C := by
  have hC : 0 ≤ C := (by positivity : 0 ≤ c₁ * p * Real.sqrt κ).trans hfirst
  have hsquare := pow_le_pow_left₀ (by positivity : 0 ≤ c₁*p*Real.sqrt κ) hfirst 2
  have hcube := mul_le_mul hsquare hsecond
    (by positivity : 0 ≤ c₂ * κ / (p^2*Λ)) (sq_nonneg C)
  have hcancel : (c₁*p*Real.sqrt κ)^2 * (c₂*κ/(p^2*Λ)) = c₁^2*c₂*κ^2/Λ := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hκ.le]
    field_simp
  rw [hcancel] at hcube
  have hpow (x : ℝ) (hx : 0 ≤ x) (k : ℝ) :
      (x ^ (k/3)) ^ (3 : ℕ) = x ^ k := by
    rw [← Real.rpow_mul_natCast hx]
    congr 1
    norm_num
  have ht : (c₁ ^ (2/3 : ℝ) * c₂ ^ (1/3 : ℝ) * κ ^ (2/3 : ℝ) /
      Λ ^ (1/3 : ℝ)) ^ (3 : ℕ) = c₁^2*c₂*κ^2/Λ := by
    rw [div_pow, mul_pow, mul_pow, hpow c₁ hc₁.le 2, hpow c₂ hc₂.le 1,
      hpow κ hκ.le 2, hpow Λ hΛ.le 1]
    norm_num
  have htarget : 0 ≤ c₁ ^ (2/3 : ℝ) * c₂ ^ (1/3 : ℝ) * κ ^ (2/3 : ℝ) /
      Λ ^ (1/3 : ℝ) := by positivity
  by_contra! hbad
  have hstrict := pow_lt_pow_left₀ hbad hC (by decide : (3 : ℕ) ≠ 0)
  rw [ht] at hstrict
  nlinarith

end
end BreakingResonance
