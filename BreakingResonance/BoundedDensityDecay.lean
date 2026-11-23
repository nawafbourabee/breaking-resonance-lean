import BreakingResonance.ReversibleDensities
import BreakingResonance.RestrictedPoincare
import BreakingResonance.MixingRecurrence

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ProbabilityTheory ENNReal

namespace BreakingResonance

variable {S : Type*} [MeasurableSpace S]

theorem markovDirichlet_congr_ae
    (π : Measure S) [IsProbabilityMeasure π] (P : Kernel S S) [IsMarkovKernel P]
    (hP : P.Invariant π) {f g : S → ℝ} (he : f =ᵐ[π] g) :
    markovDirichlet π P f = markovDirichlet π P g := by
  have hfst : MeasurePreserving Prod.fst (π ⊗ₘ P) π :=
    ⟨measurable_fst, Measure.fst_compProd π P⟩
  have hsnd := kernel_snd_measurePreserving π P hP
  have h := ((hfst.quasiMeasurePreserving.ae_eq_comp he).sub
    (hsnd.quasiMeasurePreserving.ae_eq_comp he)).mono fun _ e => congrArg (·^2) e
  exact congrArg ((1/2) * ·) (integral_congr_ae h)

theorem densityIterate_integral_eq
    (π : Measure S) [IsProbabilityMeasure π] (P : Kernel S S) [IsMarkovKernel P]
    (hP : P.Invariant π) {f : S → ℝ} (hf : Measurable f) {C : ℝ}
    (h0 : ∀ x, 0 ≤ f x) (hC : ∀ x, f x ≤ C) :
    ∀ k, (∫ x, densityIterate P f k x ∂π) = ∫ x, f x ∂π := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk := densityIterate_bounded P hf h0 hC k
    exact (markovAction_integral_eq π P hP
      (markovAction_integrable_bound hk.1 hk.2.1 hk.2.2)).trans ih

/-- Decay of the squared L² error for an initial density bounded by C. -/
theorem bounded_density_decay
    (π : Measure S) [IsProbabilityMeasure π] (P : Kernel S S) [IsMarkovKernel P]
    (hrev : P.IsReversible π) {s β φ C : ℝ} (hs : 0 ≤ s) (hβ : 0 ≤ β)
    (hβ₁ : β ≤ 1) (hφ : 0 < φ) (hφ₁ : φ ≤ 1) (hcond : RestrictedConductance π P s φ)
    (hspec : ∀ f : Lp ℝ 2 π,
      β*markovDirichlet π P f ≤ ‖f‖^2-‖markovL2 π P hrev.invariant f‖^2)
    {f : S → ℝ} (hf : Measurable f) (h0 : ∀ x, 0 ≤ f x) (hC : ∀ x, f x ≤ C)
    (hmean : (∫ x, f x ∂π) = 1) (n : ℕ) :
    (∫ x, (densityIterate P f n x-1)^2 ∂π) ≤
      Real.exp (-(n:ℝ)*β*φ^2/2)*C+2*s*C^2 := by
  let F := densityIterate P f
  let V (k : ℕ) := ∫ x, (F k x-1)^2 ∂π
  let D (k : ℕ) := markovDirichlet π P (F k)
  have hF (k) := densityIterate_bounded P hf h0 hC k
  have hmeanF (k : ℕ) : (∫ x, F k x ∂π) = 1 :=
    (densityIterate_integral_eq π P hrev.invariant hf h0 hC k).trans hmean
  have hLp (k : ℕ) : MemLp (F k) 2 π := memLp_of_bounded
    (Filter.Eventually.of_forall fun x => ⟨(hF k).2.1 x,(hF k).2.2 x⟩)
    (hF k).1.aestronglyMeasurable 2
  have hpoinc (k : ℕ) : V k ≤ 2/φ^2*D k+2*s*C^2 := by
    have h := restrictedConductance_variance_le π P hrev hs hφ hcond
      (hF k).1 (hF k).2.1 (hF k).2.2
    rw [variance_eq_integral (hF k).1.aemeasurable,hmeanF k] at h
    exact h
  have hdec (k : ℕ) : β*D k ≤ V k-V (k+1) := by
    let g (x : S) := F k x-1
    have hg : MemLp g 2 π := (hLp k).sub (memLp_const 1)
    let a := hg.toLp g
    have ha : ⇑a =ᵐ[π] g := hg.coeFn_toLp
    have hap : ⇑(markovL2 π P hrev.invariant a) =ᵐ[π] markovAction P g :=
      (markovL2_apply_ae π P hrev.invariant a).trans (markovAction_congr π P hrev.invariant ha)
    have he (x : S) : markovAction P g x = F (k+1) x-1 := by
      have hi := markovAction_integrable_bound (π := P x) (hF k).1 (hF k).2.1 (hF k).2.2
      change (∫ y, F k y-1 ∂P x) = (∫ y, F k y ∂P x)-1
      rw [integral_sub hi (integrable_const (1:ℝ)), integral_const,probReal_univ,one_smul]
    have hz : markovDirichlet π P a = D k := by
      rw [markovDirichlet_congr_ae π P hrev.invariant ha]
      unfold markovDirichlet D
      congr 1
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by dsimp [g]; ring
    have h1 : ‖a‖^2 = V k := by
      rw [realLp_norm_sq]
      exact integral_congr_ae (ha.mono fun _ hx => congrArg (·^2) hx)
    have h2 : ‖markovL2 π P hrev.invariant a‖^2 = V (k+1) := by
      rw [realLp_norm_sq]
      exact integral_congr_ae (hap.mono fun x hx => congrArg (·^2) (hx.trans (he x)))
    simpa only [hz,h1,h2] using hspec a
  let : Nonempty S := nonempty_of_isProbabilityMeasure π
  have hnn : 0 ≤ C := (h0 (Classical.arbitrary S)).trans (hC (Classical.arbitrary S))
  have hbase : V 0 ≤ C := by
    have hvar := variance_eq_sub (hLp 0)
    rw [hmeanF 0, variance_eq_integral (hF 0).1.aemeasurable,hmeanF 0] at hvar
    have hbound : (∫ x, (F 0 x)^2 ∂π) ≤ C := by
      have hi := (memLp_two_iff_integrable_sq (hLp 0).aestronglyMeasurable).mp (hLp 0)
      have hj := (markovAction_integrable_bound (π := π) (hF 0).1 (hF 0).2.1 (hF 0).2.2).const_mul C
      calc
        _ ≤ ∫ x, C*F 0 x ∂π := integral_mono hi hj fun x => by
          nlinarith only [mul_nonneg ((hF 0).2.1 x) (sub_nonneg.mpr ((hF 0).2.2 x))]
        _ = C := by rw [integral_const_mul,hmeanF 0,mul_one]
    change V 0 = (∫ x, (F 0 x)^2 ∂π)-1^2 at hvar
    linarith only [hvar,hbound]
  let rate := β*φ^2/2
  have hrate : 0 ≤ rate := by dsimp [rate]; positivity
  have hrate₁ : rate ≤ 1 := by
    have hφsq : φ^2 ≤ 1 := by
      exact (sq_le_sq₀ hφ.le (by norm_num)).mpr hφ₁ |>.trans_eq (by norm_num)
    dsimp [rate]
    nlinarith only [mul_le_mul_of_nonneg_right hβ₁ (sq_nonneg φ), hφsq]
  have hstep (k : ℕ) : V (k+1) ≤ (1-rate)*V k+rate*(2*s*C^2) := by
    have h := variance_recurrence V D β φ s C hβ hφ hpoinc hdec k
    dsimp [rate]
    nlinarith only [h]
  have hfin := affine_decay_exp V rate C (2*s*C^2) hrate hrate₁ hnn
    (by positivity) hbase hstep n
  change V n ≤ _
  rw [show -(n:ℝ)*β*φ^2/2 = -(n:ℝ)*rate by dsimp [rate]; ring]
  exact hfin

end BreakingResonance

#print axioms BreakingResonance.bounded_density_decay
