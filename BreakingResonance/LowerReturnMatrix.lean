import BreakingResonance.LowerOrbitSigns
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

noncomputable section

open Matrix
open scoped Matrix

namespace BreakingResonance

def harmonicMatrix (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![2*Real.cos θ,-1;1,0]

def orbitC (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos θ/Real.sin θ, -1/Real.sin θ;
     1/Real.sin θ, -Real.cos θ/Real.sin θ]

def orbitVector (z : ℝ×ℝ) : Fin 2 → ℝ := ![z.1,z.2]

theorem orbitVector_injective : Function.Injective orbitVector := by
  intro z w h
  exact Prod.ext (congrFun h 0) (congrFun h 1)

theorem harmonicMatrix_act (θ : ℝ) (z : ℝ×ℝ) :
    orbitVector (harmonicStep θ z) = harmonicMatrix θ *ᵥ orbitVector z := by
  ext i
  fin_cases i <;> simp [orbitVector, harmonicMatrix, harmonicStep, Matrix.mulVec,
    dotProduct, Fin.sum_univ_two, sub_eq_add_neg]

theorem harmonicMatrix_iterate (θ : ℝ) (n : ℕ) (z : ℝ×ℝ) :
    orbitVector ((harmonicStep θ)^[n] z) = harmonicMatrix θ^n *ᵥ orbitVector z := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply',harmonicMatrix_act,ih,Matrix.mulVec_mulVec,pow_succ']

theorem harmonicMatrix_det (θ : ℝ) : (harmonicMatrix θ).det = 1 := by
  rw [harmonicMatrix,Matrix.det_fin_two_of]
  ring

theorem harmonicMatrix_decomp (θ : ℝ) (hθ : Real.sin θ ≠ 0) :
    harmonicMatrix θ = Real.cos θ • (1 : Matrix (Fin 2) (Fin 2) ℝ)+Real.sin θ • orbitC θ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [harmonicMatrix,orbitC,Matrix.smul_apply,Matrix.add_apply,Matrix.one_apply,smul_eq_mul,
      mul_div_cancel₀ _ hθ, mul_div_cancel_left₀ _ hθ, mul_inv_cancel₀ hθ,two_mul]

theorem orbitC_mul_self (θ : ℝ) (hθ : Real.sin θ ≠ 0) :
    orbitC θ * orbitC θ = -(1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [orbitC,Matrix.mul_apply,Fin.sum_univ_two,Matrix.one_apply] <;>
    field_simp [hθ] <;> nlinarith only [Real.sin_sq_add_cos_sq θ]

theorem harmonicMatrix_pow (θ : ℝ) (hθ : Real.sin θ ≠ 0) (n : ℕ) :
    harmonicMatrix θ^n =
      Real.cos ((n:ℝ)*θ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
      Real.sin ((n:ℝ)*θ) • orbitC θ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ,ih,harmonicMatrix_decomp θ hθ]
    simp only [Nat.cast_succ, add_mul, one_mul, Real.cos_add, Real.sin_add]
    simp only [add_mul,mul_add,smul_mul_assoc,mul_smul_comm,one_mul,mul_one,smul_smul,
      orbitC_mul_self θ hθ,smul_neg]
    module

end BreakingResonance

#print axioms BreakingResonance.harmonicMatrix_iterate
#print axioms BreakingResonance.harmonicMatrix_pow
