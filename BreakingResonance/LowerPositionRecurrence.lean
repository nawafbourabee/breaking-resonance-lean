import BreakingResonance.LowerScalarPotential

noncomputable section

namespace BreakingResonance

open PersistencePays

/-- Consecutive positions for scalar velocity Verlet, as in (7.5). -/
def consecutivePositions (g : ℝ → ℝ) (h : ℝ) (z : ℝ×ℝ) : ℝ×ℝ :=
  (z.1,z.1-h*z.2-h^2/2*g z.1)

def positionRecurrence (g : ℝ → ℝ) (h : ℝ) (z : ℝ×ℝ) : ℝ×ℝ :=
  (2*z.1-z.2-h^2*g z.1,z.1)

def harmonicStep (θ : ℝ) (z : ℝ×ℝ) : ℝ×ℝ :=
  (2*Real.cos θ*z.1-z.2,z.1)

def curvatureForAngle (h θ : ℝ) : ℝ :=
  4*Real.sin (θ/2)^2/h^2

theorem consecutivePositions_step (g : ℝ → ℝ) (h : ℝ) (z : ℝ×ℝ) :
    consecutivePositions g h (verlet g h z) =
      positionRecurrence g h (consecutivePositions g h z) := by
  let w := z.2-h/2*g z.1
  let x := z.1+h*w
  let v := w-h/2*g x
  change (x,x-h*v-h^2/2*g x) =
    (2*z.1-(z.1-h*z.2-h^2/2*g z.1)-h^2*g z.1,z.1)
  apply Prod.ext
  · dsimp [x,w]
    ring
  · dsimp [x,v,w]
    ring

theorem consecutivePositions_iterate (g : ℝ → ℝ) (h : ℝ) (z : ℝ×ℝ) (n : ℕ) :
    consecutivePositions g h (trajectory g h z n) =
      (positionRecurrence g h)^[n] (consecutivePositions g h z) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [trajectory_succ,consecutivePositions_step,Function.iterate_succ_apply',ih]

theorem positionRecurrence_fast_theta (h a b : ℝ) (hh : h ≠ 0) (z : ℝ×ℝ) :
    positionRecurrence (fastGradient (curvatureForAngle h b) (curvatureForAngle h a)) h z =
      if 0 ≤ z.1 then harmonicStep a z else harmonicStep b z := by
  have he (θ : ℝ) : h^2*curvatureForAngle h θ = 2-2*Real.cos θ := by
    have hc : Real.cos θ = Real.cos (θ/2)^2-Real.sin (θ/2)^2 := by
      conv_lhs => rw [show θ = 2*(θ/2) by ring,Real.cos_two_mul']
    unfold curvatureForAngle
    rw [show h^2*(4*Real.sin (θ/2)^2/h^2) = 4*Real.sin (θ/2)^2 by field_simp [hh],hc]
    nlinarith only [Real.sin_sq_add_cos_sq (θ/2)]
  by_cases hz : 0 ≤ z.1
  · simp only [positionRecurrence,fastGradient,ite_eq_left hz,harmonicStep]
    apply Prod.ext
    · simp only [Prod.fst]
      rw [← mul_assoc,he a]
      ring
    · rfl
  · simp only [positionRecurrence,fastGradient,ite_eq_right hz,harmonicStep]
    apply Prod.ext
    · simp only [Prod.fst]
      rw [← mul_assoc,he b]
      ring
    · rfl

theorem harmonic_sine_recurrence (s θ : ℝ) :
    Real.sin ((s+1)*θ) = 2*Real.cos θ*Real.sin (s*θ)-Real.sin ((s-1)*θ) := by
  rw [add_mul,one_mul,sub_mul,one_mul,Real.sin_add,Real.sin_sub]
  ring

/-- The two coordinates of the harmonic recurrence after an arbitrary
number of steps, in the form used for the sign estimates in Section 7. -/
theorem harmonic_iterate (θ : ℝ) (hθ : Real.sin θ ≠ 0) (n : ℕ) (x y : ℝ) :
    (harmonicStep θ)^[n] (x,y) =
      ((Real.sin (((n:ℝ)+1)*θ)*x-Real.sin ((n:ℝ)*θ)*y)/Real.sin θ,
       (Real.sin ((n:ℝ)*θ)*x-Real.sin (((n:ℝ)-1)*θ)*y)/Real.sin θ) := by
  induction n with
  | zero =>
    simp only [Function.iterate_zero_apply,Nat.cast_zero,zero_add,one_mul,
      zero_mul,Real.sin_zero,zero_sub,sub_zero,neg_one_mul,Real.sin_neg]
    rw [← neg_mul,neg_neg]
    field_simp
  | succ n ih =>
    rw [Function.iterate_succ_apply',ih]
    simp only [harmonicStep, Nat.cast_succ, Prod.fst, Prod.snd, add_sub_cancel_right]
    apply Prod.ext
    · simp only [Prod.fst]
      rw [harmonic_sine_recurrence ((n:ℝ)+1) θ,harmonic_sine_recurrence (n:ℝ) θ,
        show (n:ℝ)+1-1 = (n:ℝ) by ring]
      field_simp
      <;> ring
    · rfl

end BreakingResonance

#print axioms BreakingResonance.consecutivePositions_iterate
#print axioms BreakingResonance.positionRecurrence_fast_theta
#print axioms BreakingResonance.harmonic_iterate
