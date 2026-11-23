import BreakingResonance.GeneralEntropyConductance
import BreakingResonance.ConditionedCentering
import BreakingResonance.ReferenceProposalLaw
import BreakingResonance.ShellAcceptance

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory Set PersistencePays
open scoped ENNReal ProbabilityTheory Gradient

namespace BreakingResonance

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The rounded triangular reference kernel has restricted conductance
one fiftieth, with the entropy and acceptance constants of Section 6. -/
theorem triangular_reference_conductance (hPP : PPInterpolation E)
    {U : E → ℝ} {m L LH : ℝ} (a : A1 U m L) (hLH : 0 ≤ LH)
    (hlip : A2 U LH) (henergy : PPModifiedEnergy U LH) (hTI : TalagrandBound a)
    (hmin : U a.minimizer = 0)
    {h Tstar R η s : ℝ} (hh : 0 < h) (hR : 1 ≤ R) (hs : 0 < s)
    (hη : 0 < η) (hη₁ : η ≤ 1/600) (N : ℕ) (hN : 0 < N)
    (hT : (N:ℝ)*h = 4/Real.sqrt m) (hTstar : (N:ℝ)*h ≤ Tstar)
    (hbudget : h^2*(L*R+LH*Tstar*R*Real.sqrt R) ≤ η/3)
    (htail : (phaseGibbs U).real {z | R < phaseEnergy U z} ≤ η*s) :
    let hU := a.twice_contDiff.continuous.measurable
    let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
    RestrictedConductance (positionGibbs U)
      (randomizedVerletKernel U hU (gradient U) hg h (triangularCountLaw h N)) s (1/50) := by
  dsimp only
  let π := positionGibbs U
  let phase := phaseGibbs U
  let q := triangularCountLaw h N
  let g := gradient U
  let hU := a.twice_contDiff.continuous.measurable
  let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
  let : IsProbabilityMeasure π := a.gibbs_isProbabilityMeasure
  let : IsProbabilityMeasure phase := by unfold phase phaseGibbs; infer_instance
  let : IsProbabilityMeasure q := triangularCount_probability hh hN
  let aux := q.prod (stdGaussian E)
  let refresh := Kernel.const E aux
  let bar := π ⊗ₘ refresh
  let Q := verletProposal g h
  have hQ := measurable_verletProposal g hg h
  let G := verletLogAcceptance U g h
  let α := acceptProbability G
  have hG := measurable_verletLogAcceptance U hU g hg h
  have hα : Measurable α := (measurable_const.min hG.exp).ennreal_ofReal
  have hα₁ (z) : α z ≤ 1 := acceptProbability_le_one G z
  let Aenergy : Set (E×E) := {z | phaseEnergy U z ≤ R}
  let liftEnergy : Set (E×(ℕ×E)) := {z | (z.1,z.2.2) ∈ Aenergy}
  let Shell : Set (E×(ℕ×E)) := liftEnergy ∩ {z | z.2.1 ≤ N}
  have hS₀ : MeasurableSet Aenergy := measurableSet_le (measurable_phaseEnergy U hU) measurable_const
  have hLift : MeasurableSet liftEnergy := hS₀.preimage (measurable_fst.prodMk measurable_snd.snd)
  have hShell : MeasurableSet Shell := hLift.inter
    ((Set.to_countable {j : ℕ | j ≤ N}).measurableSet.preimage measurable_snd.fst)
  have hbar : bar = π.prod aux := by
    apply Measure.ext_prod
    intro A B hA hB
    change (π ⊗ₘ refresh) (A×ˢ B) = (π.prod aux) (A×ˢ B)
    rw [Measure.compProd_apply_prod hA hB,Measure.prod_prod]
    simp [refresh,mul_comm]
  have hAttach : (phase.prod q).map attachCount = bar := by
    rw [hbar]
    exact (attachCount_measurePreserving U q).map_eq
  have hcount : ∀ᵐ z ∂bar, z.2.1 ≤ N := by
    rw [← hAttach]
    apply (ae_map_iff measurable_attachCount.aemeasurable
      ((Set.to_countable {j : ℕ | j ≤ N}).measurableSet.preimage measurable_snd.fst)).mpr
    exact (measurePreserving_snd (μ := phase) (ν := q)).quasiMeasurePreserving.ae
      (triangularCount_ae_le hh N)
  have htail' : bar.real Shellᶜ ≤ η*s := by
    have hc : Shellᶜ =ᵐ[bar] liftEnergyᶜ := by
      filter_upwards [hcount] with z hz
      apply propext
      change (¬ (z ∈ liftEnergy ∧ z.2.1 ≤ N)) ↔ (¬ z ∈ liftEnergy)
      simp [hz]
    have he : bar.real Shellᶜ = bar.real liftEnergyᶜ := measureReal_congr hc
    change bar.real Shellᶜ ≤ _
    rw [he]
    change (bar liftEnergyᶜ).toReal ≤ _
    rw [← hAttach,Measure.map_apply measurable_attachCount hLift.compl,
      show attachCount ⁻¹' liftEnergyᶜ = Aenergyᶜ ×ˢ (univ : Set ℕ) by
        ext y; simp [liftEnergy,attachCount],
      Measure.prod_prod,measure_univ,mul_one]
    simpa only [Measure.real,Aenergy,compl_ofPred,not_le] using htail
  have hTstar₀ : 0 ≤ Tstar := (by positivity : 0 ≤ (N:ℝ)*h).trans hTstar
  have hηle : η ≤ 1 := hη₁.trans (by norm_num)
  have hacc (z : E×(ℕ×E)) (hz : z ∈ Shell) : ENNReal.ofReal (1-η) ≤ α z := by
    have hj := mul_le_mul_of_nonneg_right (by exact_mod_cast hz.2 : (z.2.1:ℝ) ≤ N) hh.le
    exact shell_acceptance a hmin hLH henergy hh hTstar₀ hR hη.le hηle hbudget
      z.2.1 (hj.trans hTstar) (z.1,z.2.2) hz.1
  let T := (N:ℝ)*h
  let aT := LH*T*h^2*R*Real.sqrt R
  let b := h^2*L*R
  have hL := a.L_pos
  have hR₀ : 0 ≤ R := by linarith
  have hsum : aT+b ≤ η/3 := by
    have hm := mul_le_mul_of_nonneg_left hTstar (show 0 ≤ LH*h^2*R*Real.sqrt R by positivity)
    dsimp [aT,b,T]
    nlinarith only [hbudget,hm]
  have ha₀ : 0 ≤ aT := by dsimp [aT,T]; positivity
  have hb₀ : 0 ≤ b := by dsimp [b]; positivity
  have hstep : h*Real.sqrt L ≤ 1 := by
    have hm := mul_le_mul_of_nonneg_left hR (show 0 ≤ h^2*L by positivity)
    change h^2*L*1 ≤ b at hm
    apply (sq_le_sq₀ (by positivity : 0 ≤ h*Real.sqrt L) (by norm_num : (0:ℝ) ≤ 1)).mp
    rw [mul_pow,Real.sq_sqrt hL.le]
    linarith only [hm,hsum,ha₀,hηle]
  have hbudget' : 2*aT+b/2 ≤ R := by linarith only [hsum,hb₀,hR,hηle]
  have hTlow : 2/Real.sqrt m ≤ (N:ℝ)*h := by
    rw [hT]
    gcongr
    norm_num
  intro A hA hsA hAh
  have hsA' : s ≤ π.real A := by
    have ht := ENNReal.toReal_mono (measure_ne_top π A) hsA
    rwa [ENNReal.toReal_ofReal hs.le] at ht
  have hAh' : π.real A ≤ 1/2 := by
    have ht := ENNReal.toReal_mono (by norm_num : (1/2:ℝ≥0∞) ≠ ⊤) hAh
    rw [ENNReal.toReal_div,ENNReal.toReal_one,ENNReal.toReal_ofNat] at ht
    exact ht
  have hηlt : η < 1 := by linarith only [hη₁]
  have hηp : 0 < 1-η := sub_pos.mpr hηlt
  let φ₀ : ℝ := 1/(50*(1-η)^2)
  have hφ : 0 < φ₀ := by dsimp [φ₀]; positivity
  have hφmax : φ₀ ≤ (1-41/48)/2 := by
    dsimp [φ₀]
    apply (div_le_iff₀ (show 0 < 50*(1-η)^2 by positivity)).mpr
    nlinarith only [hη₁,sq_nonneg η]
  have hthreshold : Real.binEntropy φ₀+(41/48)*η/(1-η)+49*η/72 ≤ (1-41/48)*Real.log 2 := by
    have h := conductance_entropy_margin hη hη₁
    dsimp [φ₀]
    have he : (41:ℝ)/48*η/(1-η) = 41*η/(48*(1-η)) := by field_simp
    rw [he]
    linarith only [h]
  have hraw (A' : Set E) (hA' : MeasurableSet A') (hAs : s ≤ π.real A') (hhalf : π.real A' ≤ 1/2) :
      let pA := cond bar ((Prod.fst ⁻¹' A') ∩ Shell)
      klDiv (pA.map Q) π ≤ ENNReal.ofReal (41/48)*klDiv pA bar+ENNReal.ofReal (49*η/72) := by
    let E₀ := energyEvent U A' R
    let D : Set (E×(ℕ×E)) := {z | (z.1,z.2.2) ∈ E₀}
    let D' : Set (E×(ℕ×E)) := (Prod.fst ⁻¹' A') ∩ Shell
    have hE₀ := energyEvent_measurable U hU A' hA' R
    have hD : MeasurableSet D := hE₀.preimage (measurable_fst.prodMk measurable_snd.snd)
    have hD' : MeasurableSet D' := (hA'.preimage measurable_fst).inter hShell
    have hcong : D' =ᵐ[bar] D := by
      filter_upwards [hcount] with z hz
      apply propext
      change (z.1 ∈ A' ∧ phaseEnergy U (z.1,z.2.2) ≤ R ∧ z.2.1 ≤ N) ↔
        (z.1 ∈ A' ∧ phaseEnergy U (z.1,z.2.2) ≤ R)
      simp [hz]
    have hmass : bar D' = phase E₀ := by
      rw [measure_congr hcong,← hAttach,Measure.map_apply measurable_attachCount hD,
        show attachCount ⁻¹' D = E₀ ×ˢ (univ : Set ℕ) by ext y; simp [D,attachCount],
        Measure.prod_prod,measure_univ,mul_one]
    have hpos : 0 < phase.real E₀ := by
      let B : Set (E×E) := Prod.fst ⁻¹' A'
      have hB : phase.real B = π.real A' := by
        have hm := congrArg ENNReal.toReal (Measure.map_apply (μ := phase) measurable_fst hA')
        change phase.fst.real A' = phase.real B at hm
        rw [show phase.fst = π from measurePreserving_fst.map_eq] at hm
        exact hm.symm
      have hp : phase.real E₀ + phase.real (B\Aenergy) = phase.real B :=
        measureReal_inter_add_sdiff hS₀
      have hdiff : phase.real (B\Aenergy) ≤ phase.real Aenergyᶜ :=
        measureReal_mono fun _ hx => hx.2
      have htail₀ : phase.real Aenergyᶜ ≤ η*s := by
        simpa only [Aenergy,compl_ofPred,not_le] using htail
      have hm := mul_le_mul_of_nonneg_left hAs hη.le
      have hprod := mul_pos (show 0 < 1-η by linarith only [hη₁]) (hs.trans_le hAs)
      nlinarith only [hB,hp,hdiff,htail₀,hm,hprod]
    have hn : phase E₀ ≠ 0 := by
      intro hz
      change 0 < (phase E₀).toReal at hpos
      simp [hz] at hpos
    have hn' : bar D' ≠ 0 := hmass.symm ▸ hn
    let μ : ProbabilityMeasure (E×E) := ⟨cond phase E₀,cond_isProbabilityMeasure hn⟩
    have hce : cond bar D' = ((μ : Measure (E×E)).prod q).map attachCount := by
      rw [show cond bar D' = cond bar D by
        rw [ProbabilityTheory.cond,ProbabilityTheory.cond,measure_congr hcong,
          Measure.restrict_congr_set hcong]]
      rw [hbar]
      exact attachCount_condition U q E₀ hE₀
    have hsupp : ∀ᵐ z ∂(μ : Measure (E×E)), phaseEnergy U z ≤ R := by
      change ∀ᵐ z ∂cond phase E₀, _
      rw [ProbabilityTheory.cond]
      apply Measure.ae_smul_measure _ _
      filter_upwards [ae_restrict_mem (μ := phase) hE₀] with z hz
      exact hz.2
    have hK := conditionedGibbs_entropy a A' hA' R hn
    have hKbar := conditional_klDiv_self bar D' hD' hn'
    have hsame : klDiv (μ : Measure (E×E)) phase = klDiv (cond bar D') bar := by
      apply (ENNReal.toReal_eq_toReal_iff' hK.1 hKbar.1).mp
      rw [hK.2,hKbar.2,hmass]
    have hcenter := conditionedGibbs_centered U hU a.gibbs_integrable A' hA' R hn
    have hprop := verlet_triangular_proposal_entropy hPP a hLH hlip henergy hTI hmin
      hh hR hstep N hTlow hbudget' μ hsupp hK.1 hcenter
    change klDiv ((cond bar D').map Q) π ≤ _
    conv_lhs => rw [hce,triangular_attached_proposal g hg μ hh N]
    apply hprop.trans
    have hco : 5/6+1/(3*m*T^2) = (41:ℝ)/48 := by
      have hms := Real.sq_sqrt a.m_pos.le
      dsimp [T]
      rw [hT]
      field_simp [a.m_pos.ne', (Real.sqrt_pos.mpr a.m_pos).ne']
      nlinarith only [hms]
    change ENNReal.ofReal ((5/6+1/(3*m*T^2))*(klDiv (μ : Measure (E×E)) phase).toReal+
      5/3*aT+49/24*b) ≤ _
    rw [hco,hsame]
    have hrhs : ENNReal.ofReal ((41:ℝ)/48)*klDiv (cond bar D') bar+ENNReal.ofReal (49*η/72) =
        ENNReal.ofReal ((41/48)*(klDiv (cond bar D') bar).toReal+49*η/72) := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 41/48),ENNReal.ofReal_toReal hKbar.1]
    rw [hrhs]
    exact ENNReal.ofReal_le_ofReal (by linarith only [hsum,ha₀])
  have hexit := general_entropy_conductance π refresh Q hQ α hα hα₁ hShell hs hη
    (by linarith only [hη₁]) (by norm_num : (0:ℝ) ≤ 41/48)
    (by norm_num : (41:ℝ)/48 < 1) (by positivity : 0 ≤ 49*η/72)
    htail' hacc hraw A hA hsA' hAh' hφ hφmax hthreshold
  have hcancel : (1-η)^2*φ₀ = (1:ℝ)/50 := by
    dsimp [φ₀]
    field_simp [hηp.ne']
  rw [hcancel] at hexit
  change ENNReal.ofReal (1/50 : ℝ)*π A ≤
    (π ⊗ₘ conditionalMetropolisKernel Q hQ α hα refresh) (A×ˢ Aᶜ)
  have hp : IsMarkovKernel (conditionalMetropolisKernel Q hQ α hα refresh) :=
    conditionalMetropolisKernel_markov Q hQ α hα hα₁ refresh
  rw [← ENNReal.ofReal_toReal (measure_ne_top π A),← ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤1/50),
    ← ENNReal.ofReal_toReal (measure_ne_top (π ⊗ₘ conditionalMetropolisKernel Q hQ α hα refresh) _)]
  exact ENNReal.ofReal_le_ofReal hexit

end BreakingResonance

#print axioms BreakingResonance.triangular_reference_conductance
