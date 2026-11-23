import PersistencePays.Volume

/-! Actual iterated velocity Verlet maps. These results establish trajectory
algebra, not the probability-kernel mixing theorems. -/
namespace BreakingResonance
noncomputable section
open PersistencePays
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def trajectory (g : E → E) (h : ℝ) (z : E × E) (n : ℕ) : E × E :=
  (verlet g h)^[n] z

@[simp] theorem trajectory_zero (g : E → E) (h : ℝ) (z : E × E) :
    trajectory g h z 0 = z := rfl

@[simp] theorem trajectory_succ (g : E → E) (h : ℝ) (z : E × E) (n : ℕ) :
    trajectory g h z (n+1) = verlet g h (trajectory g h z n) := by
  exact Function.iterate_succ_apply' (verlet g h) n z

def modifiedEnergy (U : E → ℝ) (g : E → E) (h : ℝ) (z : E × E) : ℝ :=
  phaseEnergy U z - gradientCorrection g h z.1

theorem modifiedEnergy_increment (U : E → ℝ) (g : E → E) (h : ℝ) (z : E × E) :
    modifiedEnergy U g h (verlet g h z) - modifiedEnergy U g h z =
      trapezoidDefect U g z.1 (verlet g h z).1 := by
  unfold modifiedEnergy
  linarith [verlet_energy_identity U g h z]

theorem modifiedEnergy_telescope (U : E → ℝ) (g : E → E) (h : ℝ)
    (z : E × E) (n : ℕ) :
    modifiedEnergy U g h (trajectory g h z n) - modifiedEnergy U g h z =
      ∑ i ∈ Finset.range n,
        trapezoidDefect U g (trajectory g h z i).1 (trajectory g h z (i+1)).1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have he := modifiedEnergy_increment U g h (trajectory g h z n)
    rw [trajectory_succ]
    linarith

theorem trajectory_flip (g : E → E) (h : ℝ) (z : E × E) (n : ℕ) :
    velocityFlip (trajectory g h z n) = trajectory g (-h) (velocityFlip z) n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [trajectory_succ, velocityFlip_verlet, ih]

theorem trajectory_inverse (g : E → E) (h : ℝ) (z : E × E) (n : ℕ) :
    trajectory g (-h) (trajectory g h z n) n = z := by
  have hi : Function.LeftInverse (verlet g (-h)) (verlet g h) := verlet_inverse g h
  exact hi.iterate n z

theorem flipped_trajectory_involutive (g : E → E) (h : ℝ) (n : ℕ) :
    Function.Involutive (fun z => velocityFlip (trajectory g h z n)) := by
  intro z
  change velocityFlip (trajectory g h (velocityFlip (trajectory g h z n)) n) = z
  rw [trajectory_flip, velocityFlip_involutive]
  exact trajectory_inverse g h z n

theorem quadratic_modifiedEnergy_conserved (A : E →ₗ[ℝ] E) (b : E) (c h : ℝ)
    (hA : ∀ x y, inner (𝕜 := ℝ) (A x) y = inner (𝕜 := ℝ) x (A y))
    (z : E × E) (n : ℕ) :
    modifiedEnergy (quadraticPotential A b c) (fun x => A x + b) h
      (trajectory (fun x => A x + b) h z n) =
    modifiedEnergy (quadraticPotential A b c) (fun x => A x + b) h z := by
  have he := modifiedEnergy_telescope (quadraticPotential A b c) (fun x => A x + b) h z n
  simp only [quadratic_trapezoidDefect A b c hA, Finset.sum_const_zero] at he
  linarith

theorem modifiedEnergy_increment_bound [CompleteSpace E] (U : E → ℝ) (g : E → E)
    (A : E → E →L[ℝ] E) (hgrad : ∀ x, HasGradientAt U (g x) x)
    (hHess : ∀ x, HasFDerivAt g (A x) x) (hA : Continuous A) (LH h : ℝ) (hh : 0 ≤ h)
    (hLip : ∀ x y, ‖A x - A y‖ ≤ LH * ‖x - y‖) (z : E × E) :
    |modifiedEnergy U g h (verlet g h z) - modifiedEnergy U g h z| ≤
      LH / 12 * h ^ 3 * ‖flightVelocity g h z‖ ^ 3 := by
  rw [modifiedEnergy_increment]
  exact verlet_trapezoidDefect_lipschitz_bound U g A hgrad hHess hA LH h hh hLip z

def metropolisAcceptance (U : E → ℝ) (g : E → E) (h : ℝ)
    (z : E × E) (n : ℕ) : ℝ :=
  min 1 (Real.exp (phaseEnergy U z - phaseEnergy U (trajectory g h z n)))

theorem metropolisAcceptance_lower (U : E → ℝ) (g : E → E) (h : ℝ)
    (z : E × E) (n : ℕ) (η : ℝ) (hη : 0 ≤ η)
    (herr : phaseEnergy U (trajectory g h z n) - phaseEnergy U z ≤ η) :
    1 - η ≤ metropolisAcceptance U g h z n := by
  have he : Real.exp (-η) ≤
      Real.exp (phaseEnergy U z - phaseEnergy U (trajectory g h z n)) :=
    Real.exp_le_exp.mpr (by linarith)
  have ht := Real.add_one_le_exp (-η)
  exact le_min (by linarith) (by linarith)

section Measure
open MeasureTheory
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem trajectory_measurePreserving (g : E → E) (hg : Measurable g) (h : ℝ) (n : ℕ) :
    MeasurePreserving (fun z => trajectory g h z n)
      ((volume : Measure E).prod volume) ((volume : Measure E).prod volume) := by
  exact (verlet_measurePreserving g hg h).iterate n

theorem flipped_trajectory_measurePreserving (g : E → E) (hg : Measurable g)
    (h : ℝ) (n : ℕ) :
    MeasurePreserving (fun z => velocityFlip (trajectory g h z n))
      ((volume : Measure E).prod volume) ((volume : Measure E).prod volume) :=
  velocityFlip_measurePreserving.comp (trajectory_measurePreserving g hg h n)
end Measure

end
end BreakingResonance
