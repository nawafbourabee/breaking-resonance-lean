import BreakingResonance.KernelQuadratic
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.InnerProductSpace.Positive

/-! The real L² operator of an invariant Markov kernel. -/
noncomputable section
namespace BreakingResonance
open MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory InnerProductSpace RealInnerProductSpace

variable {S : Type*} [MeasurableSpace S]

def markovAction (P : Kernel S S) (f : S → ℝ) (x : S) : ℝ :=
  ∫ y, f y ∂P x

variable (π : Measure S) [IsProbabilityMeasure π]
variable (P : Kernel S S) [IsMarkovKernel P] (hP : P.Invariant π)
include hP

theorem kernel_snd_measurePreserving :
    MeasurePreserving Prod.snd (π ⊗ₘ P) π := by
  refine ⟨measurable_snd, ?_⟩
  change (π ⊗ₘ P).snd = π
  rw [Measure.snd_compProd]
  exact hP

theorem markovAction_congr {f g : S → ℝ} (he : f =ᵐ[π] g) :
    markovAction P f =ᵐ[π] markovAction P g := by
  have h := (kernel_snd_measurePreserving π P hP).quasiMeasurePreserving.ae_eq_comp he
  filter_upwards [Measure.ae_ae_of_ae_compProd h] with x hx
  exact integral_congr_ae hx

omit [IsProbabilityMeasure π] [IsMarkovKernel P] in
theorem markovAction_integrable {f : S → ℝ} (hf : Integrable f π) :
    Integrable (markovAction P f) π := by
  have hi : Integrable f ((P ∘ₖ Kernel.const Unit π) ()) := by
    rw [Kernel.comp_const, Kernel.const_apply,hP.def]
    exact hf
  exact hi.integral_comp

omit [IsProbabilityMeasure π] [IsMarkovKernel P] in
theorem markovAction_integral_eq {f : S → ℝ} (hf : Integrable f π) :
    (∫ x, markovAction P f x ∂π) = ∫ x, f x ∂π := by
  have hi : Integrable f ((P ∘ₖ Kernel.const Unit π) ()) := by
    rw [Kernel.comp_const, Kernel.const_apply,hP.def]
    exact hf
  have he := Kernel.integral_comp hi
  rw [Kernel.comp_const, Kernel.const_apply,hP.def,Kernel.const_apply] at he
  exact he.symm

omit [IsProbabilityMeasure π] [IsMarkovKernel P] in
theorem markovAction_ae_integrable {f : S → ℝ} (hf : Integrable f π) :
    ∀ᵐ x ∂π, Integrable f (P x) := by
  have hi : Integrable f (P ∘ₘ π) := hP.def.symm ▸ hf
  exact Measure.ae_integrable_of_integrable_comp hi

theorem markovAction_sq_ae_le {f : S → ℝ} (hf : MemLp f 2 π) :
    ∀ᵐ x ∂π, (markovAction P f x)^2 ≤ markovAction P (fun y => (f y)^2) x := by
  have hf₂ := (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mp hf
  filter_upwards [markovAction_ae_integrable π P hP (hf.integrable (by norm_num)),
    markovAction_ae_integrable π P hP hf₂] with x hfi hgi
  have hcv : ConvexOn ℝ (univ : Set ℝ) (fun t : ℝ => t^2) :=
    (by decide : Even (2 : ℕ)).convexOn_pow
  exact hcv.map_integral_le (continuous_id.pow 2).continuousOn isClosed_univ
    (Filter.Eventually.of_forall fun _ => mem_univ _) hfi hgi

theorem markovAction_memLp {f : S → ℝ} (hf : MemLp f 2 π) :
    MemLp (markovAction P f) 2 π := by
  have hf₂ := (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mp hf
  have hi := markovAction_integrable π P hP (hf.integrable (by norm_num))
  apply (memLp_two_iff_integrable_sq hi.aestronglyMeasurable).mpr
  refine (markovAction_integrable π P hP hf₂).mono' (hi.aestronglyMeasurable.pow 2) ?_
  filter_upwards [markovAction_sq_ae_le π P hP hf] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact hx

theorem markovAction_integral_sq_le {f : S → ℝ} (hf : MemLp f 2 π) :
    (∫ x, (markovAction P f x)^2 ∂π) ≤ ∫ x, (f x)^2 ∂π := by
  have hf₂ := (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mp hf
  have hg := markovAction_memLp π P hP hf
  rw [← markovAction_integral_eq π P hP hf₂]
  exact integral_mono_ae ((memLp_two_iff_integrable_sq hg.aestronglyMeasurable).mp hg)
    (markovAction_integrable π P hP hf₂) (markovAction_sq_ae_le π P hP hf)

omit hP [IsProbabilityMeasure π] in
/-- The squared real L² norm written as an integral. -/
theorem realLp_norm_sq (f : Lp ℝ 2 π) : ‖f‖^2 = ∫ x, (f x)^2 ∂π := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [Real.inner_apply,pow_two]

def markovL2Linear : Lp ℝ 2 π →ₗ[ℝ] Lp ℝ 2 π where
  toFun f := (markovAction_memLp π P hP (Lp.memLp f)).toLp (markovAction P f)
  map_add' f g := by
    apply Lp.ext
    refine (MemLp.coeFn_toLp _).trans ?_
    refine (markovAction_congr π P hP (Lp.coeFn_add f g)).trans ?_
    refine Filter.EventuallyEq.trans ?_
      ((Lp.coeFn_add _ _).trans ((MemLp.coeFn_toLp _).add (MemLp.coeFn_toLp _))).symm
    filter_upwards [markovAction_ae_integrable π P hP ((Lp.memLp f).integrable (by norm_num)),
      markovAction_ae_integrable π P hP ((Lp.memLp g).integrable (by norm_num))] with x hf hg
    exact integral_add hf hg
  map_smul' c f := by
    apply Lp.ext
    refine (MemLp.coeFn_toLp _).trans ?_
    refine (markovAction_congr π P hP (Lp.coeFn_smul c f)).trans ?_
    refine Filter.EventuallyEq.trans ?_
      ((Lp.coeFn_smul c _).trans ((MemLp.coeFn_toLp _).const_smul c)).symm
    exact Filter.Eventually.of_forall fun x => integral_const_mul c (⇑f)

theorem markovL2Linear_apply_ae (f : Lp ℝ 2 π) :
    ⇑(markovL2Linear π P hP f) =ᵐ[π] markovAction P f :=
  (markovAction_memLp π P hP (Lp.memLp f)).coeFn_toLp

theorem markovL2Linear_norm_le (f : Lp ℝ 2 π) :
    ‖markovL2Linear π P hP f‖ ≤ ‖f‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [realLp_norm_sq, realLp_norm_sq]
  have h := markovL2Linear_apply_ae π P hP f
  calc
    _ = ∫ x, (markovAction P f x)^2 ∂π := integral_congr_ae (h.mono fun _ hx => by rw [hx])
    _ ≤ _ := markovAction_integral_sq_le π P hP (Lp.memLp f)

/-- Acting by integration against P(x,dy) defines a contraction on real L²(π). -/
def markovL2 : Lp ℝ 2 π →L[ℝ] Lp ℝ 2 π :=
  (markovL2Linear π P hP).mkContinuous 1 fun f => by
    simpa only [one_mul] using markovL2Linear_norm_le π P hP f

theorem markovL2_apply_ae (f : Lp ℝ 2 π) :
    ⇑(markovL2 π P hP f) =ᵐ[π] markovAction P f := markovL2Linear_apply_ae π P hP f

theorem markovL2_norm_le (f : Lp ℝ 2 π) :
    ‖markovL2 π P hP f‖ ≤ ‖f‖ := markovL2Linear_norm_le π P hP f

theorem markovL2_inner_compProd (f g : Lp ℝ 2 π) :
    ⟪f, markovL2 π P hP g⟫_ℝ = ∫ z : S×S, f z.1*g z.2 ∂(π ⊗ₘ P) := by
  have hfst : MeasurePreserving Prod.fst (π ⊗ₘ P) π :=
    ⟨measurable_fst, Measure.fst_compProd π P⟩
  have hsnd := kernel_snd_measurePreserving π P hP
  have hi : Integrable (fun z : S × S => f z.1 * g z.2) (π ⊗ₘ P) :=
    ((Lp.memLp f).comp_measurePreserving hfst).integrable_mul
      ((Lp.memLp g).comp_measurePreserving hsnd)
  rw [L2.inner_def, Measure.integral_compProd hi]
  simp_rw [integral_const_mul]
  apply integral_congr_ae
  filter_upwards [markovL2_apply_ae π P hP g] with x hx
  simp only [Real.inner_apply,hx,markovAction]

theorem markovL2_inner_quadratic (f : Lp ℝ 2 π) :
    ⟪f, markovL2 π P hP f⟫_ℝ = kernelQuadratic π P f :=
  markovL2_inner_compProd π P hP f f

omit hP in
theorem reversible_compProd_map_swap (hrev : P.IsReversible π) :
    (π ⊗ₘ P).map Prod.swap = π ⊗ₘ P := by
  apply Measure.ext_prod
  intro A B hA hB
  rw [Measure.map_apply measurable_swap (hA.prod hB)]
  have hswap : Prod.swap ⁻¹' (A ×ˢ B) = B ×ˢ A := by
    ext z
    simp [and_comm]
  rw [hswap,Measure.compProd_apply_prod hB hA,Measure.compProd_apply_prod hA hB]
  exact hrev hB hA

theorem markovL2_symmetric (hrev : P.IsReversible π) : (markovL2 π P hP).IsSymmetric := by
  intro f g
  have hfst : MeasurePreserving Prod.fst (π ⊗ₘ P) π :=
    ⟨measurable_fst, Measure.fst_compProd π P⟩
  have hsnd := kernel_snd_measurePreserving π P hP
  let F (z : S×S) := g z.1*f z.2
  have hi : Integrable F (π ⊗ₘ P) :=
    ((Lp.memLp g).comp_measurePreserving hfst).integrable_mul
      ((Lp.memLp f).comp_measurePreserving hsnd)
  have hswap := reversible_compProd_map_swap π P hrev
  let Q := markovL2 π P hP
  change ⟪Q f,g⟫_ℝ = ⟪f,Q g⟫_ℝ
  rw [real_inner_comm g (Q f)]
  change ⟪g,markovL2 π P hP f⟫_ℝ = ⟪f,markovL2 π P hP g⟫_ℝ
  rw [markovL2_inner_compProd π P hP, markovL2_inner_compProd π P hP]
  calc
    (∫ z, F z ∂(π ⊗ₘ P)) = ∫ z, F z ∂((π ⊗ₘ P).map Prod.swap) := by rw [hswap]
    _ = ∫ z, F (Prod.swap z) ∂(π ⊗ₘ P) :=
      integral_map measurable_swap.aemeasurable (by rw [hswap]; exact hi.aestronglyMeasurable)
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall fun _ => mul_comm _ _)

omit hP [IsProbabilityMeasure π] [IsMarkovKernel P] in
/-- The Dirichlet form as the integral of the squared difference under stationary flow. -/
def markovDirichlet (f : S → ℝ) : ℝ :=
  (1/2)*∫ z : S×S, (f z.1-f z.2)^2 ∂(π ⊗ₘ P)

theorem markovDirichlet_eq_norm_sub (f : Lp ℝ 2 π) :
    markovDirichlet π P f = ‖f‖^2-⟪f,markovL2 π P hP f⟫_ℝ := by
  have hfst : MeasurePreserving Prod.fst (π ⊗ₘ P) π :=
    ⟨measurable_fst, Measure.fst_compProd π P⟩
  have hsnd := kernel_snd_measurePreserving π P hP
  let g (x : S) := (f x)^2
  have hi : Integrable g π := (memLp_two_iff_integrable_sq (Lp.memLp f).aestronglyMeasurable).mp
    (Lp.memLp f)
  have hfi : Integrable (fun z : S × S => g z.1) (π ⊗ₘ P) :=
    hfst.integrable_comp_of_integrable hi
  have hsi : Integrable (fun z : S × S => g z.2) (π ⊗ₘ P) :=
    hsnd.integrable_comp_of_integrable hi
  have hp := compProd_integrable_quadratic π P hP (⇑f) (Lp.memLp f)
  have h₁ : (∫ z : S×S, g z.1 ∂(π ⊗ₘ P)) = ∫ x, g x ∂π := by
    calc
      _ = ∫ x, g x ∂((π ⊗ₘ P).map Prod.fst) :=
        (integral_map measurable_fst.aemeasurable (by rw [hfst.map_eq]; exact hi.aestronglyMeasurable)).symm
      _ = _ := by rw [hfst.map_eq]
  have h₂ : (∫ z : S×S, g z.2 ∂(π ⊗ₘ P)) = ∫ x, g x ∂π := by
    calc
      _ = ∫ x, g x ∂((π ⊗ₘ P).map Prod.snd) :=
        (integral_map measurable_snd.aemeasurable (by rw [hsnd.map_eq]; exact hi.aestronglyMeasurable)).symm
      _ = _ := by rw [hsnd.map_eq]
  have he (z : S×S) : (f z.1-f z.2)^2 = g z.1+g z.2-2*(f z.1*f z.2) := by
    unfold g
    ring
  rw [markovDirichlet, realLp_norm_sq, markovL2_inner_quadratic, kernelQuadratic]
  simp_rw [he]
  have hadd : (∫ z : S×S, g z.1+g z.2 ∂(π ⊗ₘ P)) =
      (∫ z : S×S, g z.1 ∂(π ⊗ₘ P)) + (∫ z : S×S, g z.2 ∂(π ⊗ₘ P)) :=
    integral_add hfi hsi
  have hsub : (∫ z : S×S, g z.1+g z.2-2*(f z.1*f z.2) ∂(π ⊗ₘ P)) =
      (∫ z : S×S, g z.1+g z.2 ∂(π ⊗ₘ P)) -
        (∫ z : S×S, 2*(f z.1*f z.2) ∂(π ⊗ₘ P)) :=
    integral_sub (hfi.add hsi) (hp.const_mul 2)
  rw [hsub,hadd,integral_const_mul,h₁,h₂]
  change (1/2)*((∫ x, g x ∂π)+(∫ x, g x ∂π)-2*_) = (∫ x, g x ∂π)-_
  ring

end BreakingResonance

#print axioms BreakingResonance.markovL2_norm_le
#print axioms BreakingResonance.markovL2_inner_quadratic
#print axioms BreakingResonance.markovL2_symmetric
#print axioms BreakingResonance.markovDirichlet_eq_norm_sub
