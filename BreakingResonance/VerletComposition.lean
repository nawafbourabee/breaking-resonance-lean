import BreakingResonance.TrajectoryEntropy
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Function.L2Space

/-! The unitary pullback by a Verlet step on complex Lebesgue L². -/
noncomputable section
namespace BreakingResonance
open MeasureTheory
open scoped ENNReal

variable {S : Type*} [MeasurableSpace S]

def lpCompositionEquiv (μ : Measure S) (F : S ≃ᵐ S)
    (hF : MeasurePreserving F μ μ) : Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 μ where
  __ := Lp.compMeasurePreservingₗᵢ ℂ F hF
  invFun := Lp.compMeasurePreserving F.symm (hF.symm F)
  left_inv := by
    intro v
    change Lp.compMeasurePreserving F.symm (hF.symm F)
      (Lp.compMeasurePreserving F hF v) = v
    rw [← Lp.compMeasurePreserving_comp_apply v hF (hF.symm F)]
    have he : (F : S → S) ∘ F.symm = id := funext F.apply_symm_apply
    simp [he]
  right_inv := by
    intro v
    change Lp.compMeasurePreserving F hF
      (Lp.compMeasurePreserving F.symm (hF.symm F) v) = v
    rw [← Lp.compMeasurePreserving_comp_apply v (hF.symm F) hF]
    have he : (F.symm : S → S) ∘ F = id := funext F.symm_apply_apply
    simp [he]

def lpCompositionUnitary (μ : Measure S) (F : S ≃ᵐ S)
    (hF : MeasurePreserving F μ μ) : unitary (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) :=
  Unitary.linearIsometryEquiv.symm (lpCompositionEquiv μ F hF)

theorem lpCompositionUnitary_pow_apply_ae (μ : Measure S) (F : S ≃ᵐ S)
    (hF : MeasurePreserving F μ μ) (j : ℕ) (v : Lp ℂ 2 μ) :
    ((↑((lpCompositionUnitary μ F hF)^j) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) v :
      S → ℂ) =ᵐ[μ] v ∘ (F : S → S)^[j] := by
  let U := lpCompositionUnitary μ F hF
  have hu (g : Lp ℂ 2 μ) : (↑U : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) g =
      Lp.compMeasurePreserving F hF g := by
    rfl
  induction j generalizing v with
  | zero => simp
  | succ j ih =>
    change ((↑(U^(j+1)) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) v : S → ℂ) =ᵐ[μ] _
    rw [pow_succ']
    change ((↑U : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
      ((↑(U^j) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) v) : S → ℂ) =ᵐ[μ] _
    rw [hu]
    exact (Lp.coeFn_compMeasurePreserving _ hF).trans
      (hF.quasiMeasurePreserving.ae_eq_comp (ih v) |>.trans
        (Filter.Eventually.of_forall fun z => by simp))

section Verlet

open PersistencePays

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def verletCompositionUnitary (g : E → E) (hg : Measurable g) (h : ℝ) :
    let μ := (volume : Measure E).prod (volume : Measure E)
    unitary (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) :=
  lpCompositionUnitary _ (trajectoryEquiv g hg h 1)
    (trajectory_measurePreserving g hg h 1)

end Verlet
end BreakingResonance
