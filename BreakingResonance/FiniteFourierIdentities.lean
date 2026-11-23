import BreakingResonance.FourierTrig

/-! Finite cosine sums for the uniform and triangular duration laws. -/
noncomputable section
namespace BreakingResonance

/-- Mean cosine at the two rounded endpoints of cell j. -/
def cellCosine (θ : ℝ) (j : ℕ) : ℝ :=
  (Real.cos ((j : ℝ)*θ) + Real.cos (((j : ℝ)+1)*θ))/2

/-- The numerator for the triangular law, before division by N². -/
def triangularCosineNumerator (θ : ℝ) (N : ℕ) : ℝ :=
  ∑ j ∈ Finset.range N, (2*((N : ℝ)-j)-1) * cellCosine θ j

theorem cellCosine_succ_add (θ : ℝ) (j : ℕ) :
    cellCosine θ j + cellCosine θ (j+1) =
      (1 + Real.cos θ) * Real.cos (((j : ℝ)+1)*θ) := by
  have hc : Real.cos ((j : ℝ)*θ) + Real.cos (((j : ℝ)+2)*θ) =
      2 * Real.cos (((j : ℝ)+1)*θ) * Real.cos θ := by
    rw [show (j : ℝ)*θ = ((j : ℝ)+1)*θ - θ by ring,
      show ((j : ℝ)+2)*θ = ((j : ℝ)+1)*θ + θ by ring, Real.cos_sub, Real.cos_add]
    ring
  simp only [cellCosine, Nat.cast_add, Nat.cast_one]
  rw [show (j : ℝ)+1+1 = (j : ℝ)+2 by ring]
  linarith only [hc]

theorem triangularCosineNumerator_succ (θ : ℝ) (N : ℕ) :
    triangularCosineNumerator θ (N+1) - triangularCosineNumerator θ N =
      2 * (∑ j ∈ Finset.range N, cellCosine θ j) + cellCosine θ N := by
  unfold triangularCosineNumerator
  rw [Finset.sum_range_succ]
  push_cast
  have hf (j : ℕ) : (2*((N : ℝ)+1-j)-1) * cellCosine θ j =
      (2*((N : ℝ)-j)-1) * cellCosine θ j + 2 * cellCosine θ j := by ring
  simp only [hf, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

theorem triangularCosineNumerator_second_difference (θ : ℝ) (N : ℕ) :
    triangularCosineNumerator θ (N+2) -
      2*triangularCosineNumerator θ (N+1) + triangularCosineNumerator θ N =
      (1+Real.cos θ) * Real.cos (((N : ℝ)+1)*θ) := by
  have h₀ := triangularCosineNumerator_succ θ N
  have h₁ := triangularCosineNumerator_succ θ (N+1)
  rw [Finset.sum_range_succ] at h₁
  linarith only [h₀, h₁, cellCosine_succ_add θ N]

theorem one_sub_cosine_count_second_difference (θ : ℝ) (N : ℕ) :
    (1-Real.cos (((N : ℝ)+2)*θ)) - 2*(1-Real.cos (((N : ℝ)+1)*θ)) +
      (1-Real.cos ((N : ℝ)*θ)) =
      2*(1-Real.cos θ)*Real.cos (((N : ℝ)+1)*θ) := by
  rw [show ((N : ℝ)+2)*θ = ((N : ℝ)+1)*θ + θ by ring,
    show (N : ℝ)*θ = ((N : ℝ)+1)*θ - θ by ring, Real.cos_add, Real.cos_sub]
  ring

/-- This identity is the real Fourier transform in Appendix C before
using half-angle formulas or dividing by N². -/
theorem triangularCosineNumerator_identity (θ : ℝ) (N : ℕ) :
    2*(1-Real.cos θ) * triangularCosineNumerator θ N =
      (1+Real.cos θ) * (1-Real.cos ((N : ℝ)*θ)) := by
  let a (j : ℕ) := 2*(1-Real.cos θ) * triangularCosineNumerator θ j
  let b (j : ℕ) := (1+Real.cos θ) * (1-Real.cos ((j : ℝ)*θ))
  have hab (j : ℕ) : a j = b j ∧ a (j+1) = b (j+1) := by
    induction j with
    | zero =>
      constructor
      · simp [a, b, triangularCosineNumerator]
      · simp only [a, b, Nat.cast_one, one_mul, triangularCosineNumerator,
          Finset.sum_range_one, Nat.cast_zero, sub_zero, cellCosine, zero_mul, Real.cos_zero,
          zero_add]
        ring
    | succ j ih =>
      refine ⟨ih.2, ?_⟩
      have hae : a (j+2)-2*a (j+1)+a j =
          2*(1-Real.cos θ)*((1+Real.cos θ)*Real.cos (((j : ℝ)+1)*θ)) := by
        dsimp only [a]
        linear_combination (2*(1-Real.cos θ)) * triangularCosineNumerator_second_difference θ j
      have hbe : b (j+2)-2*b (j+1)+b j =
          (1+Real.cos θ)*(2*(1-Real.cos θ)*Real.cos (((j : ℝ)+1)*θ)) := by
        dsimp only [b]
        push_cast
        linear_combination (1+Real.cos θ)*one_sub_cosine_count_second_difference θ j
      rw [ih.1, ih.2] at hae
      have hs : a (j+2) = b (j+2) := by
        linear_combination hae - hbe
      exact hs
  exact (hab N).1

theorem cellCosine_sine_increment (θ : ℝ) (j : ℕ) :
    2 * Real.sin θ * cellCosine θ j =
      (1 + Real.cos θ) * (Real.sin (((j : ℝ)+1)*θ) - Real.sin ((j : ℝ)*θ)) := by
  unfold cellCosine
  rw [add_mul, one_mul, Real.cos_add, Real.sin_add]
  linear_combination -(Real.sin ((j : ℝ)*θ)) * Real.sin_sq_add_cos_sq θ

/-- The mean cosine for uniform rounding intervals telescopes to sin(Nθ). -/
theorem uniformCosine_sum_identity (θ : ℝ) (N : ℕ) :
    2 * Real.sin θ * (∑ j ∈ Finset.range N, cellCosine θ j) =
      (1+Real.cos θ) * Real.sin ((N : ℝ)*θ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, mul_add, ih, cellCosine_sine_increment]
    push_cast
    ring

end BreakingResonance

#print axioms BreakingResonance.triangularCosineNumerator_identity
#print axioms BreakingResonance.uniformCosine_sum_identity
