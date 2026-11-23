import BreakingResonance.ConditionalMetropolis
import BreakingResonance.EntropyExitGeneral

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory Set PersistencePays
open scoped ENNReal ProbabilityTheory

namespace BreakingResonance

variable {S V : Type*} [MeasurableSpace S] [MeasurableSpace V]

/-- Lemma 6.9. The conditional refreshment kernel represents the
conditional law in (6.29). The joint reference law is its composition
product with the position marginal. -/
theorem general_entropy_conductance
    (π : Measure S) [IsProbabilityMeasure π] (refresh : Kernel S V) [IsMarkovKernel refresh]
    (Q : S×V → S) (hQ : Measurable Q) (α : S×V → ℝ≥0∞) (hα : Measurable α)
    (hα₁ : ∀ z, α z ≤ 1) {Shell : Set (S×V)} (hShell : MeasurableSet Shell)
    {s η θ δ₀ : ℝ} (hs : 0 < s) (hη : 0 < η) (hη₁ : η < 1)
    (hθ : 0 ≤ θ) (_hθ₁ : θ < 1) (hδ : 0 ≤ δ₀)
    (htail : (π ⊗ₘ refresh).real Shellᶜ ≤ η*s)
    (hacc : ∀ z ∈ Shell, ENNReal.ofReal (1-η) ≤ α z)
    (hentropy : ∀ A : Set S, MeasurableSet A → s ≤ π.real A → π.real A ≤ 1/2 →
      let pA := cond (π ⊗ₘ refresh) ((Prod.fst ⁻¹' A) ∩ Shell)
      klDiv (pA.map Q) π ≤ ENNReal.ofReal θ * klDiv pA (π ⊗ₘ refresh) + ENNReal.ofReal δ₀)
    (A : Set S) (hA : MeasurableSet A) (hAs : s ≤ π.real A) (hAh : π.real A ≤ 1/2)
    {φ₀ : ℝ} (hφ : 0 < φ₀) (hφθ : φ₀ ≤ (1-θ)/2)
    (hthreshold : Real.binEntropy φ₀+θ*η/(1-η)+δ₀ ≤ (1-θ)*Real.log 2) :
    (1-η)^2*φ₀*π.real A ≤ (π ⊗ₘ conditionalMetropolisKernel Q hQ α hα refresh).real
      (A ×ˢ Aᶜ) := by
  let bar := π ⊗ₘ refresh
  let K := conditionalMetropolisKernel Q hQ α hα refresh
  have : IsMarkovKernel K := conditionalMetropolisKernel_markov Q hQ α hα hα₁ refresh
  let B : Set (S×V) := Prod.fst ⁻¹' A
  let E := B ∩ Shell
  have hBm : MeasurableSet B := hA.preimage measurable_fst
  have hEm : MeasurableSet E := hBm.inter hShell
  have hB : bar.real B = π.real A := by
    have h := Measure.map_apply (μ := bar) measurable_fst hA
    have h := congrArg ENNReal.toReal h
    change bar.fst.real A = bar.real B at h
    rw [Measure.fst_compProd] at h
    exact h.symm
  have hBsplit : bar.real E+bar.real (B\Shell) = bar.real B :=
    measureReal_inter_add_sdiff hShell
  have hdiff : bar.real (B\Shell) ≤ bar.real Shellᶜ :=
    measureReal_mono fun _ hz => hz.2
  have hmass : (1-η)*π.real A ≤ bar.real E := by
    have hm := mul_le_mul_of_nonneg_left hAs hη.le
    nlinarith only [hB,hBsplit,hdiff,htail,hm]
  have hApos := hs.trans_le hAs
  have hηp : 0 < 1-η := sub_pos.mpr hη₁
  have hEpos : 0 < bar.real E := (mul_pos hηp hApos).trans_le hmass
  have hEnz : bar E ≠ 0 := by
    intro h
    change (0:ℝ) < (bar E).toReal at hEpos
    simp [h] at hEpos
  let pA := cond bar E
  have : IsProbabilityMeasure pA := cond_isProbabilityMeasure hEnz
  let ν := pA.map Q
  have : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map hQ.aemeasurable
  have hself := conditional_klDiv_self bar E hEm hEnz
  have hu := hentropy A hA hAs hAh
  change klDiv ν π ≤ ENNReal.ofReal θ*klDiv pA bar+ENNReal.ofReal δ₀ at hu
  have hK : klDiv ν π ≠ ⊤ := ne_top_of_le_ne_top (by finiteness [hself.1]) hu
  have huR := ENNReal.toReal_mono (by finiteness [hself.1]) hu
  rw [ENNReal.toReal_add (by finiteness [hself.1]) (by finiteness),ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hθ,ENNReal.toReal_ofReal hδ,hself.2] at huR
  have hcap := mul_le_mul_of_nonneg_left
    (conditional_entropy_upper hη hη₁ hApos hmass) hθ
  have hexit := entropy_forces_exit_general ν π hK A hA hApos hAh hθ hφ hφθ
    (show (klDiv ν π).toReal ≤ θ*Real.log (1/π.real A)+(θ*η/(1-η)+δ₀) by
      calc
        _ ≤ θ*(-Real.log (bar.real E))+δ₀ := huR
        _ ≤ θ*(Real.log (1/π.real A)+η/(1-η))+δ₀ := add_le_add hcap le_rfl
        _ = _ := by ring)
    (by linarith only [hthreshold])
  have heq : (bar E)*(ν Aᶜ) = bar (E ∩ Q ⁻¹' Aᶜ) := by
    change bar E*(pA.map Q) Aᶜ = _
    rw [Measure.map_apply hQ hA.compl,mul_comm]
    exact cond_mul_eq_inter hEm _ _
  let Vout := (Aᶜ).indicator (fun _ : S => (1:ℝ≥0∞))
  have hm : Measurable (fun z : S×V => Vout (Q z)) :=
    (measurable_const.indicator hA.compl).comp hQ
  have hmeasure : ENNReal.ofReal (1-η)*bar (E ∩ Q ⁻¹' Aᶜ) =
      ∫⁻ z in E, ENNReal.ofReal (1-η)*Vout (Q z) ∂bar := by
    rw [lintegral_const_mul _ hm,show (fun z => Vout (Q z)) =
      (Q ⁻¹' Aᶜ).indicator (fun _ => (1:ℝ≥0∞)) from rfl,
      lintegral_indicator_const (hA.compl.preimage hQ),one_mul,
      Measure.restrict_apply (hA.compl.preimage hQ),inter_comm]
  have ht : ENNReal.ofReal (1-η)*bar E*ν Aᶜ ≤ (π ⊗ₘ K) (A ×ˢ Aᶜ) := by
    rw [mul_assoc,heq,hmeasure,conditionalMetropolisKernel_exit_flow π Q hQ α hα hα₁ refresh A hA]
    calc
      _ ≤ ∫⁻ z in E, A.indicator (fun _ => 1) z.1*(α z*Vout (Q z)) ∂bar := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem hEm] with z hz
        rw [indicator_of_mem (show z.1 ∈ A from hz.1),one_mul]
        exact mul_le_mul' (hacc z hz.2) le_rfl
      _ ≤ _ := lintegral_mono' Measure.restrict_le_self le_rfl
  have htr := ENNReal.toReal_mono (measure_ne_top (π ⊗ₘ K) _) ht
  rw [ENNReal.toReal_mul,ENNReal.toReal_mul,ENNReal.toReal_ofReal hηp.le] at htr
  change (1-η)*bar.real E*ν.real Aᶜ ≤ _ at htr
  have hle := mul_le_mul hmass hexit hφ.le (by positivity)
  have hz := mul_le_mul_of_nonneg_left hle hηp.le
  change _ ≤ ((π ⊗ₘ K) (A ×ˢ Aᶜ)).toReal
  nlinarith only [htr,hz]

end BreakingResonance

#print axioms BreakingResonance.general_entropy_conductance
