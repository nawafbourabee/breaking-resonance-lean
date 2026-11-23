import BreakingResonance.RejectionBounds
import Mathlib.Probability.Kernel.IonescuTulcea.Traj

noncomputable section

open MeasureTheory ProbabilityTheory Set PersistencePays Preorder
open scoped ENNReal ProbabilityTheory

namespace BreakingResonance

variable {S : Type*} [MeasurableSpace S]

def lastPathPosition (i : ℕ) (x : Finset.Iic i → S) : S := x ⟨i,Finset.mem_Iic.mpr le_rfl⟩

theorem lastPathPosition_measurable (i : ℕ) : Measurable (lastPathPosition (S := S) i) :=
  measurable_pi_apply _

def markovPathTransitions (P : Kernel S S) (i : ℕ) : Kernel (Finset.Iic i → S) S :=
  P.comap (lastPathPosition i) (lastPathPosition_measurable i)

instance (P : Kernel S S) [IsMarkovKernel P] (i : ℕ) :
    IsMarkovKernel (markovPathTransitions P i) := by
  unfold markovPathTransitions
  infer_instance

def markovPathLaw (P : Kernel S S) [IsMarkovKernel P] (ν : Measure S) : Measure (ℕ → S) :=
  Kernel.trajMeasure (X := fun _ => S) ν (markovPathTransitions P)

theorem markovPathLaw_zero (P : Kernel S S) [IsMarkovKernel P] (ν : Measure S) :
    (markovPathLaw P ν).map (Function.eval 0) = ν := by
  let e : (Finset.Iic (0:ℕ) → S) ≃ᵐ S := MeasurableEquiv.piUnique _
  have he : (Function.eval 0 : (ℕ → S) → S) = e ∘ (frestrictLe 0) := by
    funext x
    change x 0 = x (default : Finset.Iic (0:ℕ))
    rfl
  rw [he,← Measure.map_map e.measurable (measurable_frestrictLe 0),
    markovPathLaw,Kernel.trajMeasure,Measure.map_comp _ _ (measurable_frestrictLe 0),
    Kernel.traj_map_frestrictLe,Kernel.partialTraj_self,Measure.id_comp]
  exact e.map_map_symm

theorem markovPathLaw_cross_two (P : Kernel S S) [IsMarkovKernel P] (ν : Measure S)
    [IsProbabilityMeasure ν] (i : ℕ) {A B : Set S} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    markovPathLaw P ν {x | x i ∈ A ∧ x (i+1) ∈ B} =
      ∫⁻ x in A, P x B ∂((markovPathLaw P ν).map (Function.eval i)) := by
  let μ := markovPathLaw P ν
  let f := lastPathPosition (S := S) i
  let r := frestrictLe (π := fun _ : ℕ => S) i
  have hf : Measurable f := lastPathPosition_measurable i
  have hr : Measurable r := measurable_frestrictLe i
  have : IsProbabilityMeasure μ := by unfold μ markovPathLaw; infer_instance
  have : IsProbabilityMeasure (μ.map r) := Measure.isProbabilityMeasure_map hr.aemeasurable
  let C := f ⁻¹' A
  have hC : MeasurableSet C := hA.preimage hf
  have hF : Measurable (fun x : ℕ → S => (r x,x (i+1))) :=
    hr.prodMk (measurable_pi_apply _)
  have hEq := Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
    (X := fun _ : ℕ => S) (μ₀ := ν) (κ := markovPathTransitions P) (a := i)
  change μ.map r ⊗ₘ markovPathTransitions P i =
    μ.map (fun x => (r x,x (i+1))) at hEq
  change μ ((fun x : ℕ → S => (r x,x (i+1))) ⁻¹' (C ×ˢ B)) = _
  rw [← Measure.map_apply hF (hC.prod hB),← hEq,Measure.compProd_apply_prod hC hB]
  change (∫⁻ x in C, P (f x) B ∂μ.map r) = _
  rw [← setLIntegral_map hA (P.measurable_coe hB) hf,Measure.map_map hf hr]
  rfl

theorem markovPathLaw_marginal (P : Kernel S S) [IsMarkovKernel P] (ν : Measure S)
    [IsProbabilityMeasure ν] (n : ℕ) :
    (markovPathLaw P ν).map (Function.eval n) = evolve (fun _ => P) ν n := by
  induction n with
  | zero => exact markovPathLaw_zero P ν
  | succ n ih =>
    ext B hB
    rw [Measure.map_apply (measurable_pi_apply (n+1)) hB,evolve_succ,
      Measure.bind_apply hB P.aemeasurable]
    have he : (Function.eval (n+1)) ⁻¹' B =
        {x : ℕ → S | x n ∈ (univ : Set S) ∧ x (n+1) ∈ B} := by ext x; simp [Function.eval]
    rw [he,markovPathLaw_cross_two P ν n MeasurableSet.univ hB,setLIntegral_univ,ih]

omit [MeasurableSpace S] in
/-- A path starting in A must cross from A to its complement before it
can end outside A. -/
theorem exit_subset_crossings (A : Set S) (n : ℕ) :
    {x : ℕ → S | x 0 ∈ A ∧ x n ∉ A} ⊆
      ⋃ i ∈ Finset.range n, {x : ℕ → S | x i ∈ A ∧ x (i+1) ∉ A} := by
  intro x hx
  have hstart := hx.1
  have hend := hx.2
  induction n with
  | zero => exact (hend hstart).elim
  | succ n ih =>
    by_cases hcur : x n ∈ A
    · exact mem_iUnion.mpr ⟨n,mem_iUnion.mpr ⟨Finset.mem_range.mpr n.lt_succ_self,⟨hcur,hend⟩⟩⟩
    · exact (iUnion₂_mono' (fun i hi => ⟨i,Finset.mem_range.mpr
        ((Finset.mem_range.mp hi).trans n.lt_succ_self),subset_rfl⟩)) (ih ⟨hstart,hcur⟩ hcur)

theorem markovPathLaw_exit_le_crossing_sum (P : Kernel S S) [IsMarkovKernel P] (ν : Measure S)
    [IsProbabilityMeasure ν] {A : Set S} (hA : MeasurableSet A) (hν : ν Aᶜ = 0) (n : ℕ) :
    (evolve (fun _ => P) ν n) Aᶜ ≤
      ∑ i ∈ Finset.range n, ∫⁻ x in A, P x Aᶜ ∂(evolve (fun _ => P) ν i) := by
  let μ := markovPathLaw P ν
  have hzero : μ {x | x 0 ∉ A} = 0 := by
    change μ ((Function.eval 0) ⁻¹' Aᶜ) = 0
    rw [← Measure.map_apply (measurable_pi_apply _) hA.compl,markovPathLaw_zero,hν]
  have hpath :
      μ {x | x n ∉ A} = μ {x | x 0 ∈ A ∧ x n ∉ A} := by
    apply measure_congr
    have hpos : ∀ᵐ x ∂μ, x 0 ∈ A := (ae_iff (μ := μ)).mpr hzero
    filter_upwards [hpos] with x hx
    change (x n ∉ A) = (x 0 ∈ A ∧ x n ∉ A)
    simp [hx]
  rw [← markovPathLaw_marginal P ν n,Measure.map_apply (measurable_pi_apply _) hA.compl]
  change μ {x | x n ∉ A} ≤ _
  rw [hpath]
  refine (measure_mono (exit_subset_crossings A n)).trans (le_trans (measure_biUnion_finset_le _ _) ?_)
  apply Finset.sum_le_sum
  intro i _
  change μ {x | x i ∈ A ∧ x (i+1) ∈ Aᶜ} ≤ _
  rw [markovPathLaw_cross_two P ν i hA hA.compl,markovPathLaw_marginal]

end BreakingResonance

#print axioms BreakingResonance.markovPathLaw_marginal
#print axioms BreakingResonance.exit_subset_crossings
#print axioms BreakingResonance.markovPathLaw_exit_le_crossing_sum
