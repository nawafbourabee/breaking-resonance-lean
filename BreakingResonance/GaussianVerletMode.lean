import BreakingResonance.LowerProductDynamics
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

noncomputable section

open PersistencePays

namespace BreakingResonance

private theorem quadraticForce (c : ℝ) :
    fastGradient c c = fun x => c*x := by
  funext x
  simp [fastGradient]

theorem gaussianVerlet_angle {a : ℝ} (ha : 0 < a) (ha₁ : a ≤ 1) :
    let r := Real.sqrt (1-a^2/4)
    let θ := 2*Real.arcsin (a/2)
    0 < r ∧ r ≤ 1 ∧ 3/4 ≤ r^2 ∧ 0 < θ ∧ θ ≤ a/r ∧
      Real.cos θ = 1-a^2/2 ∧ Real.sin θ = a*r := by
  let r := Real.sqrt (1-a^2/4)
  let u := Real.arcsin (a/2)
  let θ := 2*u
  have ha₂ : a^2 ≤ 1 := by simpa using (sq_le_sq₀ ha.le zero_le_one).mpr ha₁
  have hs₀ : 0 < 1-a^2/4 := by linarith only [ha₂]
  have hr : 0 < r := Real.sqrt_pos.mpr hs₀
  have hr₁ : r ≤ 1 := (sq_le_sq₀ hr.le zero_le_one).mp (by
    rw [Real.sq_sqrt hs₀.le]
    nlinarith only [sq_nonneg a])
  have hu : 0 < u := Real.arcsin_pos.mpr (by positivity : 0 < a/2)
  have hul : u < Real.pi/2 := Real.arcsin_lt_pi_div_two.mpr (by linarith only [ha₁])
  have hsin : Real.sin u = a/2 := Real.sin_arcsin (by linarith only [ha])
    (by linarith only [ha₁])
  have hcos : Real.cos u = r := by
    rw [Real.cos_arcsin]
    congr 1
    ring
  have ht := Real.le_tan hu.le hul
  rw [Real.tan_eq_sin_div_cos,hsin,hcos] at ht
  change 0 < r ∧ r ≤ 1 ∧ 3/4 ≤ r^2 ∧ 0 < θ ∧ θ ≤ a/r ∧
    Real.cos θ = 1-a^2/2 ∧ Real.sin θ = a*r
  refine ⟨hr,hr₁,?_,by positivity,?_,?_,?_⟩
  · rw [Real.sq_sqrt hs₀.le]
    linarith only [ha₂]
  · unfold θ
    rw [show a/2/r = (a/r)/2 by ring] at ht
    linarith only [ht]
  · unfold θ
    rw [Real.cos_two_mul, hcos, Real.sq_sqrt hs₀.le]
    ring
  · unfold θ
    rw [Real.sin_two_mul,hsin,hcos]
    ring

set_option maxHeartbeats 800000 in
/-- The actual velocity Verlet proposal in one quadratic coordinate, in
the standard normal position units used in Appendix B. -/
theorem gaussianVerlet_position {m h : ℝ} (hm : 0 < m) (hh : 0 < h)
    (ha₁ : h*Real.sqrt m ≤ 1) (z : ℝ×ℝ) (j : ℕ) :
    let a := h*Real.sqrt m
    let r := Real.sqrt (1-a^2/4)
    let θ := 2*Real.arcsin (a/2)
    Real.sqrt m*(trajectory (fastGradient m m) h z j).1 =
      Real.cos ((j:ℝ)*θ)*(Real.sqrt m*z.1)+Real.sin ((j:ℝ)*θ)/r*z.2 := by
  let a := h*Real.sqrt m
  let r := Real.sqrt (1-a^2/4)
  let θ := 2*Real.arcsin (a/2)
  let g := fastGradient m m
  have hsm : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm
  have ha : 0 < a := by positivity
  obtain ⟨hr,_,_,_,_,hcos,hsin⟩ := gaussianVerlet_angle ha ha₁
  change 0 < r at hr
  change Real.cos θ = 1-a^2/2 at hcos
  change Real.sin θ = a*r at hsin
  have hsa : Real.sin θ ≠ 0 := by rw [hsin]; exact (mul_pos ha hr).ne'
  have hA : a^2 = h^2*m := by unfold a; rw [mul_pow,Real.sq_sqrt hm.le]
  have hF : positionRecurrence g h = harmonicStep θ := by
    funext v
    unfold positionRecurrence harmonicStep
    change (2*v.1-v.2-h^2*fastGradient m m v.1,v.1) = _
    rw [quadraticForce,hcos,hA]
    congr 1
    ring
  have hy : (consecutivePositions g h z).2 = Real.cos θ*z.1-h*z.2 := by
    unfold consecutivePositions
    change z.1-h*z.2-h^2/2*(fastGradient m m z.1) = _
    rw [quadraticForce,hcos,hA]
    ring
  have hp := consecutivePositions_iterate g h z j
  rw [hF] at hp
  have hx := congrArg Prod.fst hp
  change (trajectory g h z j).1 = ((harmonicStep θ)^[j] (consecutivePositions g h z)).1 at hx
  rw [hx]
  have hpair : consecutivePositions g h z = (z.1,Real.cos θ*z.1-h*z.2) := Prod.ext rfl hy
  rw [hpair,harmonic_iterate θ hsa]
  rw [show ((j:ℝ)+1)*θ = (j:ℝ)*θ+θ by ring,Real.sin_add]
  rw [hsin]
  change Real.sqrt m*_
      = Real.cos ((j:ℝ)*θ)*(Real.sqrt m*z.1)+Real.sin ((j:ℝ)*θ)/r*z.2
  unfold a
  field_simp [hr.ne',hh.ne',hsm.ne']
  ring

end BreakingResonance

#print axioms BreakingResonance.gaussianVerlet_angle
#print axioms BreakingResonance.gaussianVerlet_position
