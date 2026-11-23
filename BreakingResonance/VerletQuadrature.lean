import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import BreakingResonance.WeightedDiscrete
import Mathlib.Tactic

/-! Exact quadrature coefficients in the weighted numerical entropy calculation. -/
namespace BreakingResonance
noncomputable section
open MeasureTheory

theorem linear_weight_integral (A h : ℝ) :
    (∫σ in (0:ℝ)..h,A-σ)=h*A-h^2/2 := by
  rw [intervalIntegral.integral_sub (f:=fun _ : ℝ=>A) (g:=fun σ : ℝ=>σ)
      intervalIntegrable_const (continuous_id.intervalIntegrable 0 h),
    intervalIntegral.integral_const,integral_id]
  simp only [sub_zero,smul_eq_mul,zero_pow (by norm_num : (2:ℕ)≠0)]

theorem weighted_centered_linear_integral (A h : ℝ) :
    (∫σ in (0:ℝ)..h,(A-σ)*(σ-h/2))= -h^3/12 := by
  have he (σ : ℝ) : (A-σ)*(σ-h/2)=(A+h/2)*σ-σ^2-A*h/2 := by ring
  simp_rw [he]
  rw [intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop) intervalIntegrable_const,
    intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop) (by apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_const_mul,integral_id,integral_pow,
    intervalIntegral.integral_const]
  simp only [sub_zero,smul_eq_mul]
  norm_num
  ring

theorem weighted_affine_integral (A h e f : ℝ) (Q : ℝ → ℝ)
    (hQ : Continuous Q) :
    (∫σ in (0:ℝ)..h,(A-σ)*(e+(σ-h/2)*f+Q σ))=
      (h*A-h^2/2)*e-h^3/12*f+(∫σ in (0:ℝ)..h,(A-σ)*Q σ) := by
  have he (σ : ℝ) : (A-σ)*(e+(σ-h/2)*f+Q σ)=
      (A-σ)*e+(A-σ)*(σ-h/2)*f+(A-σ)*Q σ := by ring
  simp_rw [he]
  rw [intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop) (by apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop) (by apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_mul_const,intervalIntegral.integral_mul_const,
    linear_weight_integral,weighted_centered_linear_integral]
  ring

theorem combine_weighted_integrals (h c : ℝ) (Q : ℝ → ℝ) (hQ : Continuous Q) :
    (∫σ in (0:ℝ)..h,(h-σ)*Q σ)+c*(∫σ in (0:ℝ)..h,Q σ)=
      ∫σ in (0:ℝ)..h,(h+c-σ)*Q σ := by
  rw [←intervalIntegral.integral_const_mul]
  rw [←intervalIntegral.integral_add
    (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop)]
  apply intervalIntegral.integral_congr
  intro σ _
  ring

def triangularWeight (h : ℝ) (N n : ℕ) : ℝ := h*(((N:ℝ)-n)*h)-h^2/2

theorem triangularWeight_nonneg {h : ℝ} {N n : ℕ} (hn : n<N) :
    0≤triangularWeight h N n := by
  have hc : (n:ℝ)+1≤N := by exact_mod_cast hn
  have hs := mul_nonneg (sub_nonneg.mpr hc) (sq_nonneg h)
  dsimp [triangularWeight]
  nlinarith [sq_nonneg h]

theorem triangularWeight_sum (h : ℝ) (N : ℕ) :
    (∑n∈Finset.range N,triangularWeight h N n)=((N:ℝ)*h)^2/2 := by
  let F : ℕ → ℝ := fun n=>(((N:ℝ)-n)*h)^2/2
  have he (n : ℕ) : triangularWeight h N n= -(F (n+1)-F n) := by
    dsimp [triangularWeight,F]
    push_cast
    ring
  simp_rw [he]
  rw [Finset.sum_neg_distrib,sum_consecutive_differences]
  dsimp [F]
  ring

theorem weighted_endpoint_quadrature (U : ℕ → ℝ) (h : ℝ) (N : ℕ) :
    (∑n∈Finset.range N,
      ((h*(((N:ℝ)-n)*h)/2-h^2/6)*U n+
      (h*(((N:ℝ)-n)*h)/2-h^2/3)*U (n+1)))=
      h*((N:ℝ)*h/2*U 0+(∑n∈Finset.range N,((N:ℝ)-(n+1))*h*U (n+1)))+
      h^2/6*(U N-U 0) := by
  let F : ℕ → ℝ := fun n=>((N:ℝ)-n)*h*U n
  have he (n : ℕ) :
      (h*(((N:ℝ)-n)*h)/2-h^2/6)*U n+
      (h*(((N:ℝ)-n)*h)/2-h^2/3)*U (n+1)=
      h*(((N:ℝ)-(n+1))*h*U (n+1))-
        h/2*(F (n+1)-F n)+h^2/6*(U (n+1)-U n) := by
    dsimp [F]
    push_cast
    ring
  simp_rw [he]
  rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,←Finset.mul_sum,
    ←Finset.mul_sum,←Finset.mul_sum,sum_consecutive_differences,sum_consecutive_differences]
  dsimp [F]
  ring

end
end BreakingResonance
