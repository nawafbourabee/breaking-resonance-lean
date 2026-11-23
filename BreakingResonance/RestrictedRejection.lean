import BreakingResonance.ConductanceTransfer

noncomputable section

open MeasureTheory ProbabilityTheory Set PersistencePays
open scoped ProbabilityTheory ENNReal

namespace BreakingResonance

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

local notation "phaseVolume" => (Measure.prod (volume : Measure E) (volume : Measure E))

/-- Express the rejected density as the Gibbs density times the rejection probability. -/
theorem rejectedVerletMeasure_eq (U : E → ℝ) (hU : Measurable U)
    (hZ : Integrable (fun x => Real.exp (-U x)) volume)
    (g : E → E) (hg : Measurable g) (h : ℝ) (j : ℕ) :
    let G (z : E×E) := phaseEnergy U z-phaseEnergy U (trajectory g h z j)
    (phaseVolume).withDensity (rejectedVerletDensity U g h j) =
      (phaseGibbs U).withDensity (fun z => 1-acceptProbability G z) := by
  let G (z : E×E) := phaseEnergy U z-phaseEnergy U (trajectory g h z j)
  let α := acceptProbability G
  let p := phaseGibbsDensity U
  have hG : Measurable G := (measurable_phaseEnergy U hU).sub
    ((measurable_phaseEnergy U hU).comp (trajectory_measurePreserving g hg h j).measurable)
  have hα : Measurable α := (measurable_const.min hG.exp).ennreal_ofReal
  have ha (z : E × E) : p z*α z = acceptedWeight p (fun z => trajectory g h z j) z := by
    dsimp only [p,α,G,phaseGibbsDensity,acceptedWeight,acceptProbability]
    rw [mul_assoc,gibbs_acceptance_identity (phaseEnergy U) (fun z => trajectory g h z j) z,mul_min]
  let β (z : E×E) := 1-α z
  have hβ : Measurable β := measurable_const.sub hα
  change _ = (phaseGibbs U).withDensity β
  rw [phaseGibbs_eq_withDensity U hU hZ,← withDensity_mul phaseVolume
    (phaseGibbsDensity_measurable U hU) hβ]
  congr 1
  funext z
  change p z-acceptedWeight p (fun z => trajectory g h z j) z = p z*(1-α z)
  rw [ENNReal.mul_sub (fun _ _ => phaseGibbsDensity_ne_top U hZ z),mul_one,ha]

/-- The rejection estimate for one integration count that is controlled on the energy shell. -/
theorem rejection_on_shell_one (U : E → ℝ) (hU : Measurable U)
    (hZ : Integrable (fun x => Real.exp (-U x)) volume)
    (g : E → E) (hg : Measurable g) (h : ℝ) (j : ℕ) {η R : ℝ} (hη : 0 ≤ η)
    (hη₁ : η ≤ 1)
    (hacc : ∀ z : E×E, phaseEnergy U z ≤ R →
      ENNReal.ofReal (1-η) ≤ acceptProbability
        (fun z => phaseEnergy U z-phaseEnergy U (trajectory g h z j)) z)
    {A : Set E} (hA : MeasurableSet A) :
    (∫ z, (A.indicator (fun _ => (1:ℝ)) z.1)^2
      ∂(phaseVolume).withDensity (rejectedVerletDensity U g h j)) ≤
      η*(positionGibbs U).real A+(phaseGibbs U).real {z | R < phaseEnergy U z} := by
  let π := positionGibbs U
  let phase := phaseGibbs U
  let : IsProbabilityMeasure π := isProbabilityMeasure_tilted hZ
  let : IsProbabilityMeasure phase := (by unfold phase phaseGibbs; infer_instance)
  let B : Set (E×E) := Prod.fst ⁻¹' A
  let high : Set (E×E) := {z | R < phaseEnergy U z}
  let G (z : E×E) := phaseEnergy U z-phaseEnergy U (trajectory g h z j)
  let α := acceptProbability G
  have hBm : MeasurableSet B := hA.preimage measurable_fst
  have hhigh : MeasurableSet high := measurableSet_lt measurable_const (measurable_phaseEnergy U hU)
  have hf (z : E×E) : (A.indicator (fun _ => (1:ℝ)) z.1)^2 = B.indicator (fun _ => 1) z := by
    by_cases hz : z.1 ∈ A <;> simp [B,hz]
  have hB : phase B = π A := by
    have h := Measure.map_apply (μ := phase) measurable_fst hA
    change phase.fst A = phase B at h
    rw [show phase.fst = π from measurePreserving_fst.map_eq] at h
    exact h.symm
  have hbound (z : E×E) : 1-α z ≤ ENNReal.ofReal η + high.indicator (fun _ => 1) z := by
    by_cases hz : R < phaseEnergy U z
    · rw [indicator_of_mem (show z ∈ high from hz)]
      exact tsub_le_self.trans le_add_self
    · rw [indicator_of_notMem (show z ∉ high from hz),add_zero]
      have hh := tsub_le_tsub_left (hacc z (le_of_not_gt hz)) 1
      rw [ENNReal.ofReal_sub 1 hη, ENNReal.ofReal_one,
        ENNReal.sub_sub_cancel ENNReal.one_ne_top (by simpa using ENNReal.ofReal_le_ofReal hη₁)] at hh
      exact hh
  have hmeasure : (∫⁻ z in B, 1-α z ∂phase) ≤ ENNReal.ofReal η*π A+phase high := by
    calc
      _ ≤ ∫⁻ z in B, ENNReal.ofReal η+high.indicator (fun _ => 1) z ∂phase :=
        lintegral_mono hbound
      _ ≤ _ := by
        rw [lintegral_add_left measurable_const,lintegral_const,lintegral_indicator_const hhigh,
          one_mul,Measure.restrict_apply_univ,hB]
        exact add_le_add le_rfl (Measure.restrict_le_self high)
  have hr := ENNReal.toReal_mono (by finiteness) hmeasure
  rw [ENNReal.toReal_add (by finiteness) (by finiteness),ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hη] at hr
  simp_rw [hf]
  rw [rejectedVerletMeasure_eq U hU hZ g hg h j,integral_indicator hBm,setIntegral_const,
    smul_eq_mul,mul_one,Measure.real,withDensity_apply _ hBm]
  exact hr

theorem rejection_on_shell_mixture (U : E → ℝ) (hU : Measurable U)
    (hZ : Integrable (fun x => Real.exp (-U x)) volume)
    (g : E → E) (hg : Measurable g) (h : ℝ) (w : Measure ℕ) [IsProbabilityMeasure w]
    {η R : ℝ} (hη : 0 ≤ η) (hη₁ : η ≤ 1)
    (hacc : ∀ᵐ j ∂w, ∀ z : E×E, phaseEnergy U z ≤ R →
      ENNReal.ofReal (1-η) ≤ acceptProbability
        (fun z => phaseEnergy U z-phaseEnergy U (trajectory g h z j)) z)
    {A : Set E} (hA : MeasurableSet A) :
    verletRejectionForm U g h w (A.indicator (fun _ => 1)) ≤
      η*(positionGibbs U).real A+(phaseGibbs U).real {z | R < phaseEnergy U z} := by
  let π := positionGibbs U
  let : IsProbabilityMeasure π := isProbabilityMeasure_tilted hZ
  let f := A.indicator (fun _ : E => (1:ℝ))
  let C := η*π.real A+(phaseGibbs U).real {z | R < phaseEnergy U z}
  have hpoint (j : ℕ) : countLawWeight w j *
      (∫ z, (f z.1)^2 ∂(phaseVolume).withDensity (rejectedVerletDensity U g h j)) ≤
        countLawWeight w j*C := by
    by_cases hj : w {j} = 0
    · simp [countLawWeight,hj]
    · have hgood : ∀ z : E×E, phaseEnergy U z ≤ R →
          ENNReal.ofReal (1-η) ≤ acceptProbability
            (fun z => phaseEnergy U z-phaseEnergy U (trajectory g h z j)) z := by
        by_contra hbad
        rw [ae_iff] at hacc
        have hs := measure_mono (μ := w) (show ({j} : Set ℕ) ⊆
            {k | ¬∀ z : E×E, phaseEnergy U z ≤ R →
              ENNReal.ofReal (1-η) ≤ acceptProbability
                (fun z => phaseEnergy U z-phaseEnergy U (trajectory g h z k)) z} from
          fun k hk => by
            have he : k = j := hk
            subst k
            exact hbad)
        exact hj (le_zero_iff.mp (hs.trans_eq hacc))
      exact mul_le_mul_of_nonneg_left (rejection_on_shell_one U hU hZ g hg h j hη hη₁ hgood hA)
        (countLawWeight_nonneg w j)
  have hm := Summable.tsum_le_tsum hpoint
    (summable_verletRejectionForm U hU hZ g h w f (measurable_const.indicator hA)
      (indicator_one_memLp π hA)) ((countLawWeight_summable w).mul_right C)
  rw [tsum_mul_right, countLawWeight_tsum, one_mul] at hm
  exact hm

end BreakingResonance

#print axioms BreakingResonance.rejection_on_shell_mixture
