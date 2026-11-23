import BreakingResonance.VerletTrajectory

/-! Energy bounds for the actual iterated Verlet map. The gradient estimate
is derived from the stated derivative and curvature hypotheses. The error
budget uses `R * sqrt R`, equal to `R^(3/2)` for nonnegative R. -/
namespace BreakingResonance
noncomputable section
open PersistencePays
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem energy_comparison (U : E → ℝ) (g : E → E) (h L : ℝ)
    (hL : 0 ≤ L) (_hU : ∀ x, 0 ≤ U x)
    (hg : ∀ x, ‖g x‖ ^ 2 ≤ 2 * L * U x) (z : E × E) :
    (1 - h ^ 2 * L / 4) * phaseEnergy U z ≤ modifiedEnergy U g h z ∧
    modifiedEnergy U g h z ≤ phaseEnergy U z := by
  rw [modifiedEnergy, phaseEnergy_eq_norm, gradientCorrection_eq_norm]
  have hp := mul_le_mul_of_nonneg_left (hg z.1) (sq_nonneg h)
  have hv : 0 ≤ h ^ 2 * L * ‖z.2‖ ^ 2 := by positivity
  constructor
  · nlinarith
  · have hc : 0 ≤ h ^ 2 / 8 * ‖g z.1‖ ^ 2 := by positivity
    linarith

theorem flightVelocity_sq_le_modifiedEnergy (U : E → ℝ) (g : E → E)
    (h L : ℝ) (_hL : 0 ≤ L) (hU : ∀ x, 0 ≤ U x)
    (hg : ∀ x, ‖g x‖ ^ 2 ≤ 2 * L * U x) (hstep : h ^ 2 * L ≤ 1)
    (z : E × E) :
    ‖flightVelocity g h z‖ ^ 2 ≤ 4 * modifiedEnergy U g h z := by
  have ht := norm_sub_le z.2 ((h / 2) • g z.1)
  have ht2 : ‖z.2 - (h / 2) • g z.1‖ ^ 2 ≤
      2 * ‖z.2‖ ^ 2 + 2 * ‖(h / 2) • g z.1‖ ^ 2 := by
    nlinarith [norm_nonneg (z.2 - (h / 2) • g z.1),
      norm_nonneg z.2, norm_nonneg ((h / 2) • g z.1),
      sq_nonneg (‖z.2‖ - ‖(h / 2) • g z.1‖)]
  rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at ht2
  have hgrad := mul_le_mul_of_nonneg_left (hg z.1) (sq_nonneg h)
  have hsmall := mul_le_mul_of_nonneg_right hstep (hU z.1)
  rw [flightVelocity, modifiedEnergy, phaseEnergy_eq_norm, gradientCorrection_eq_norm]
  nlinarith

omit [InnerProductSpace ℝ E] in
theorem norm_cube_bound {v : E} {R : ℝ} (hR : 0 ≤ R)
    (hv : ‖v‖ ^ 2 ≤ 8 * R) : ‖v‖ ^ 3 ≤ 24 * R * Real.sqrt R := by
  have hs := Real.sq_sqrt hR
  have hroot := Real.sqrt_nonneg R
  have hb : ‖v‖ ≤ 3 * Real.sqrt R := by nlinarith [norm_nonneg v]
  have hm := mul_le_mul hv hb (norm_nonneg v) (by positivity : 0 ≤ 8 * R)
  nlinarith

theorem verlet_energy_control_with_modified_error_of_remainder [CompleteSpace E]
    (U : E → ℝ) (g : E → E) (A : E → E →L[ℝ] E)
    (hgrad : ∀ x, HasGradientAt U (g x) x)
    (hHess : ∀ x, HasFDerivAt g (A x) x) (hA : Continuous A)
    (L LH h R : ℝ) (hL : 0 < L) (hLH : 0 ≤ LH) (hh : 0 ≤ h)
    (hR : 0 ≤ R) (hU : ∀ x, 0 ≤ U x)
    (hcurv : ∀ x u, inner (𝕜 := ℝ) (A x u) u ≤ L * ‖u‖ ^ 2)
    (hremainder : ∀ z, |modifiedEnergy U g h (verlet g h z) -
      modifiedEnergy U g h z| ≤ LH / 12 * h^3 * ‖flightVelocity g h z‖^3)
    (hstep : h ^ 2 * L ≤ 1) (N : ℕ)
    (hbudget : 2 * (LH * ((N : ℝ) * h) * h ^ 2 * R * Real.sqrt R) +
      (h ^ 2 * L * R) / 2 ≤ R)
    (z : E × E) (hstart : phaseEnergy U z ≤ R) :
    ∀ n ≤ N,
      modifiedEnergy U g h (trajectory g h z n) ≤
        R + 2 * (LH * ((N : ℝ) * h) * h ^ 2 * R * Real.sqrt R) ∧
      phaseEnergy U (trajectory g h z n) ≤ 2 * R ∧
      |phaseEnergy U (trajectory g h z n) - phaseEnergy U z| ≤
        2 * (LH * ((N : ℝ) * h) * h ^ 2 * R * Real.sqrt R) + h ^ 2 * L * R ∧
      ‖flightVelocity g h (trajectory g h z n)‖ ^ 2 ≤ 8 * R ∧
      modifiedEnergy U g h (trajectory g h z n) - phaseEnergy U z ≤
        2 * (LH * ((N : ℝ) * h) * h ^ 2 * R * Real.sqrt R) := by
  let a := LH * ((N : ℝ) * h) * h ^ 2 * R * Real.sqrt R
  let b := h ^ 2 * L * R
  let Δ := 2 * LH * h ^ 3 * R * Real.sqrt R
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hΔ : 0 ≤ Δ := by dsimp [Δ]; positivity
  have htotal : (N : ℝ) * Δ = 2 * a := by dsimp [Δ, a]; ring
  have hg (x : E) : ‖g x‖ ^ 2 ≤ 2 * L * U x := by
    simpa using gradient_norm_sq_le_energy U g A hgrad hHess hA L hL hcurv 0 hU x
  have hF0 : modifiedEnergy U g h z ≤ R :=
    (energy_comparison U g h L hL.le hU hg z).2.trans hstart
  have hsum (n : ℕ) (hn : n ≤ N) : (n : ℝ) * Δ ≤ 2 * a := by
    rw [← htotal]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hn) hΔ
  have hbound : ∀ n ≤ N,
      |modifiedEnergy U g h (trajectory g h z n) - modifiedEnergy U g h z| ≤
        (n : ℝ) * Δ := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      have hnp : n ≤ N := Nat.le_trans (Nat.le_succ n) hn
      have hi := ih hnp
      have hFn : modifiedEnergy U g h (trajectory g h z n) ≤ 2 * R := by
        have hupper := (abs_le.mp hi).2
        have hs := hsum n hnp
        change 2 * a + b / 2 ≤ R at hbudget
        linarith
      have hw := flightVelocity_sq_le_modifiedEnergy U g h L hL.le hU hg hstep
        (trajectory g h z n)
      have hc := norm_cube_bound hR (show ‖flightVelocity g h (trajectory g h z n)‖ ^ 2 ≤ 8 * R by linarith)
      have he := hremainder (trajectory g h z n)
      have hinc : |modifiedEnergy U g h (trajectory g h z (n+1)) -
          modifiedEnergy U g h (trajectory g h z n)| ≤ Δ := by
        rw [trajectory_succ]
        have hm := mul_le_mul_of_nonneg_left hc (by positivity : 0 ≤ LH / 12 * h ^ 3)
        dsimp [Δ]
        nlinarith
      have htri := abs_sub_le (modifiedEnergy U g h (trajectory g h z (n+1)))
        (modifiedEnergy U g h (trajectory g h z n)) (modifiedEnergy U g h z)
      push_cast
      linarith
  intro n hn
  have hi := hbound n hn
  have hs := hsum n hn
  have hF : modifiedEnergy U g h (trajectory g h z n) ≤ R + 2 * a := by
    linarith [(abs_le.mp hi).2]
  have hcomp := (energy_comparison U g h L hL.le hU hg (trajectory g h z n)).1
  have hH : phaseEnergy U (trajectory g h z n) ≤ 2 * R := by
    have hpos : 0 < 1 - h ^ 2 * L / 4 := by linarith
    apply (mul_le_mul_iff_right₀ hpos).mp
    change 2 * a + b / 2 ≤ R at hbudget
    dsimp [b] at hbudget
    nlinarith
  have hc0 := gradientCorrection_bound U g A hgrad hHess hA L hL hcurv 0 hU h z.1
  have hcn := gradientCorrection_bound U g A hgrad hHess hA L hL hcurv 0 hU h
    (trajectory g h z n).1
  have hUn : U (trajectory g h z n).1 ≤ 2 * R := by
    rw [phaseEnergy_eq_norm] at hH
    nlinarith [sq_nonneg ‖(trajectory g h z n).2‖]
  have hU0 : U z.1 ≤ R := by
    rw [phaseEnergy_eq_norm] at hstart
    nlinarith [sq_nonneg ‖z.2‖]
  have hcn' : gradientCorrection g h (trajectory g h z n).1 ≤ b / 2 := by
    have hp := mul_le_mul_of_nonneg_left hUn (by positivity : 0 ≤ h ^ 2 * L / 4)
    dsimp [b]; nlinarith [hcn.2]
  have hc0' : gradientCorrection g h z.1 ≤ b / 4 := by
    have hp := mul_le_mul_of_nonneg_left hU0 (by positivity : 0 ≤ h ^ 2 * L / 4)
    dsimp [b]; nlinarith [hc0.2]
  refine ⟨hF, hH, ?_, ?_, ?_⟩
  · change |phaseEnergy U (trajectory g h z n) - phaseEnergy U z| ≤ 2 * a + b
    rw [abs_le] at hi ⊢
    dsimp [modifiedEnergy] at hi
    constructor <;> linarith [hc0.1, hcn.1]
  · have hw := flightVelocity_sq_le_modifiedEnergy U g h L hL.le hU hg hstep
        (trajectory g h z n)
    change 2 * a + b / 2 ≤ R at hbudget
    linarith

  · have hstartComparison := (energy_comparison U g h L hL.le hU hg z).2
    exact (show modifiedEnergy U g h (trajectory g h z n) - phaseEnergy U z ≤
      (n : ℝ) * Δ by linarith only [(abs_le.mp hi).2, hstartComparison]).trans hs

theorem verlet_energy_control_with_modified_error [CompleteSpace E]
    (U : E → ℝ) (g : E → E) (A : E → E →L[ℝ] E)
    (hgrad : ∀ x, HasGradientAt U (g x) x)
    (hHess : ∀ x, HasFDerivAt g (A x) x) (hA : Continuous A)
    (L LH h R : ℝ) (hL : 0 < L) (hLH : 0 ≤ LH) (hh : 0 ≤ h)
    (hR : 0 ≤ R) (hU : ∀ x, 0 ≤ U x)
    (hcurv : ∀ x u, inner (𝕜 := ℝ) (A x u) u ≤ L * ‖u‖ ^ 2)
    (hLip : ∀ x y, ‖A x - A y‖ ≤ LH * ‖x - y‖)
    (hstep : h ^ 2 * L ≤ 1) (N : ℕ)
    (hbudget : 2 * (LH * ((N : ℝ) * h) * h ^ 2 * R * Real.sqrt R) +
      (h ^ 2 * L * R) / 2 ≤ R)
    (z : E × E) (hstart : phaseEnergy U z ≤ R) :
    ∀ n ≤ N,
      modifiedEnergy U g h (trajectory g h z n) ≤
        R + 2 * (LH * ((N : ℝ) * h) * h ^ 2 * R * Real.sqrt R) ∧
      phaseEnergy U (trajectory g h z n) ≤ 2 * R ∧
      |phaseEnergy U (trajectory g h z n) - phaseEnergy U z| ≤
        2 * (LH * ((N : ℝ) * h) * h ^ 2 * R * Real.sqrt R) + h ^ 2 * L * R ∧
      ‖flightVelocity g h (trajectory g h z n)‖ ^ 2 ≤ 8 * R ∧
      modifiedEnergy U g h (trajectory g h z n) - phaseEnergy U z ≤
        2 * (LH * ((N : ℝ) * h) * h ^ 2 * R * Real.sqrt R) :=
  verlet_energy_control_with_modified_error_of_remainder U g A hgrad hHess hA L LH h R
    hL hLH hh hR hU hcurv (modifiedEnergy_increment_bound U g A hgrad hHess hA LH h hh hLip)
    hstep N hbudget z hstart

theorem verlet_energy_control [CompleteSpace E]
    (U : E → ℝ) (g : E → E) (A : E → E →L[ℝ] E)
    (hgrad : ∀ x, HasGradientAt U (g x) x)
    (hHess : ∀ x, HasFDerivAt g (A x) x) (hA : Continuous A)
    (L LH h R : ℝ) (hL : 0 < L) (hLH : 0 ≤ LH) (hh : 0 ≤ h)
    (hR : 0 ≤ R) (hU : ∀ x, 0 ≤ U x)
    (hcurv : ∀ x u, inner (𝕜 := ℝ) (A x u) u ≤ L * ‖u‖ ^ 2)
    (hLip : ∀ x y, ‖A x - A y‖ ≤ LH * ‖x - y‖)
    (hstep : h ^ 2 * L ≤ 1) (N : ℕ)
    (hbudget : 2 * (LH * ((N : ℝ) * h) * h ^ 2 * R * Real.sqrt R) +
      (h ^ 2 * L * R) / 2 ≤ R)
    (z : E × E) (hstart : phaseEnergy U z ≤ R) :
    ∀ n ≤ N,
      modifiedEnergy U g h (trajectory g h z n) ≤
        R + 2 * (LH * ((N : ℝ) * h) * h ^ 2 * R * Real.sqrt R) ∧
      phaseEnergy U (trajectory g h z n) ≤ 2 * R ∧
      |phaseEnergy U (trajectory g h z n) - phaseEnergy U z| ≤
        2 * (LH * ((N : ℝ) * h) * h ^ 2 * R * Real.sqrt R) + h ^ 2 * L * R ∧
      ‖flightVelocity g h (trajectory g h z n)‖ ^ 2 ≤ 8 * R := by
  intro n hn
  obtain ⟨hF, hH, herror, hw, _⟩ :=
    verlet_energy_control_with_modified_error U g A hgrad hHess hA L LH h R hL hLH hh hR
      hU hcurv hLip hstep N hbudget z hstart n hn
  exact ⟨hF, hH, herror, hw⟩

end
end BreakingResonance
