import Mathlib.Tactic

/-! Finite summation of the drift and force-update inequalities. -/
namespace BreakingResonance

theorem sum_consecutive_differences (F : ℕ → ℝ) (N : ℕ) :
    (∑n∈Finset.range N,(F (n+1)-F n))=F N-F 0 := by
  induction N with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ,ih]; ring

theorem weighted_discrete_accumulation (N : ℕ) {h : ℝ} (hh : 0≤h)
    (W C I D : ℕ → ℝ)
    (hW : ∀j<N,W (j+1)-W j≤h*C j+I j)
    (hC : ∀j<N,C (j+1)-C j≤D j) :
    W N-W 0≤(N:ℝ)*h*C 0+
      ∑j∈Finset.range N,(I j+((N:ℝ)-(j+1))*h*D j) := by
  let F : ℕ → ℝ := fun j=>W j+((N:ℝ)-j)*h*C j
  have hstep : ∀j<N,F (j+1)-F j≤I j+((N:ℝ)-(j+1))*h*D j := by
    intro j hj
    have hjR : (j:ℝ)+1≤N := by exact_mod_cast hj
    have he := mul_le_mul_of_nonneg_left (hC j hj)
      (mul_nonneg (sub_nonneg.mpr hjR) hh)
    have hw := hW j hj
    dsimp [F]
    push_cast
    nlinarith
  have hsum := Finset.sum_le_sum (fun j hj=>hstep j (Finset.mem_range.mp hj))
  have htel (n : ℕ) : (∑j∈Finset.range n,(F (j+1)-F j))=F n-F 0 := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ,ih]
      ring
  rw [htel] at hsum
  dsimp [F] at hsum
  simp only [sub_self,zero_mul,Nat.cast_zero,sub_zero] at hsum
  linarith

end BreakingResonance
