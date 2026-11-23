import BreakingResonance.LowerExpandingSet
import BreakingResonance.TrajectoryEntropy
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BreakingResonance

theorem measurable_asymmetricForce (h : ℝ) (p : ℕ) (δ : ℝ) :
    Measurable (asymmetricForce h p δ) := (fastGradient_continuous _ _).measurable

theorem fastOrbit_measurableSet_image (h : ℝ) (p : ℕ) (δ : ℝ) (j : ℕ)
    {E : Set (ℝ×ℝ)} (hE : MeasurableSet E) :
    MeasurableSet ((fun z => fastOrbit h p δ z j) '' E) := by
  let e := trajectoryEquiv (asymmetricForce h p δ) (measurable_asymmetricForce h p δ) h j
  exact e.measurableSet_image.mpr hE

theorem measurableSet_expandingSet (h : ℝ) (p : ℕ) (δ : ℝ) :
    MeasurableSet (expandingSet h p δ) :=
  MeasurableSet.biUnion (Finset.range (cycleLength p)).countable_toSet
    (fun j _ => fastOrbit_measurableSet_image h p δ j (measurableSet_expandingSeed h p δ))

theorem expandingSeed_volume {h : ℝ} (hh : 0 < h) (p : ℕ) (δ : ℝ) :
    ((volume : Measure ℝ).prod volume) (expandingSeed h p δ) = ENNReal.ofReal (3*h/200) := by
  let I := Icc (h/10) (h/5)
  let a := Real.cos (fastAnglePos p δ)
  rw [Measure.prod_apply (measurableSet_expandingSeed h p δ)]
  have hs (x : ℝ) :
      volume (Prod.mk x ⁻¹' expandingSeed h p δ) =
        I.indicator (fun t => ENNReal.ofReal (t/h)) x := by
    by_cases hx : x ∈ I
    · rw [indicator_of_mem hx]
      have he : Prod.mk x ⁻¹' expandingSeed h p δ =
          Icc ((a*x+3*x)/h) ((a*x+4*x)/h) := by
        ext v
        change (h/10 ≤ x ∧ x ≤ h/5 ∧ -4*x ≤ a*x-h*v ∧ a*x-h*v ≤ -3*x)
          ↔ (a*x+3*x)/h ≤ v ∧ v ≤ (a*x+4*x)/h
        rw [div_le_iff₀ hh,le_div_iff₀ hh]
        rcases hx with ⟨hx₀,hx₁⟩
        constructor
        · rintro ⟨_,_,hl,hu⟩
          exact ⟨by linarith only [hu],by linarith only [hl]⟩
        · rintro ⟨hl,hu⟩
          exact ⟨hx₀,hx₁,by linarith only [hu],by linarith only [hl]⟩
      rw [he,Real.volume_Icc]
      congr 1
      ring
    · rw [indicator_of_notMem hx]
      have he : Prod.mk x ⁻¹' expandingSeed h p δ = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro v hv
        exact hx ⟨hv.1,hv.2.1⟩
      rw [he,measure_empty]
  simp_rw [hs]
  rw [lintegral_indicator measurableSet_Icc]
  have hi : IntegrableOn (fun x : ℝ => x/h) I := by
    apply Continuous.integrableOn_Icc
    exact continuous_id.div_const h
  have hn : 0 ≤ᵐ[volume.restrict I] fun x => x/h :=
    (ae_restrict_iff' measurableSet_Icc).mpr (ae_of_all _ (fun x hx =>
      div_nonneg ((by positivity : 0 ≤ h/10).trans hx.1) hh.le))
  rw [← ofReal_integral_eq_lintegral_ofReal hi hn]
  change ENNReal.ofReal (∫ x in Icc (h/10) (h/5), x/h) = _
  rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le (show h/10 ≤ h/5 by linarith only [hh])]
  simp_rw [div_eq_mul_inv]
  rw [intervalIntegral.integral_mul_const,integral_id]
  congr 1
  field_simp
  ring

theorem seed_has_no_second_crossing {h : ℝ} (hh : 0 < h) {p : ℕ} (hp : 7 ≤ p) {δ : ℝ}
    (hδ : 0 < δ) (hδp : δ ≤ 1/(80*(p:ℝ)^2))
    {z : ℝ×ℝ} (hz : z ∈ expandingSeed h p δ)
    {j : ℕ} (hj₀ : 0 < j) (hj : j < cycleLength p) :
    fastOrbit h p δ z j ∉ expandingSeed h p δ := by
  intro hjE
  let zz := fastPositionPair h p δ z
  let F := positionRecurrence (asymmetricForce h p δ) h
  have hzC := seed_pair_in_cone hh hz
  have hjC := seed_pair_in_cone hh hjE
  change returnCone zz at hzC
  rw [fastOrbit_pair] at hjC
  change returnCone (F^[j] zz) at hjC
  obtain ⟨_,_,hpos,hneg⟩ := cycle_blocks hh hp hδ hδp zz hzC
  by_cases hjp : j < p
  · let k := j-1
    have hks : k+1 = j := by dsimp [k]; omega
    have hk : k < p := by omega
    have h := hpos k hk
    change zz.1/2 ≤ (F^[k] zz).1 at h
    have he : (F^[j] zz).2 = (F^[k] zz).1 := by
      rw [← hks,Function.iterate_succ_apply']
      rfl
    have hneg' := hjC.2.2
    rw [he] at hneg'
    linarith only [h,hneg',hjC.1,hzC.1]
  · let k := j-p
    have hks : p+k = j := Nat.add_sub_of_le (le_of_not_gt hjp)
    have hk : k < 2*p := by unfold cycleLength at hj; omega
    have h := hneg k hk
    change (F^[p+k] zz).1 ≤ -(zz.1/2) at h
    rw [hks] at h
    linarith only [h,hjC.1,hzC.1]

theorem expandingSet_images_disjoint {h : ℝ} (hh : 0 < h) {p : ℕ} (hp : 7 ≤ p) {δ : ℝ}
    (hδ : 0 < δ) (hδp : δ ≤ 1/(80*(p:ℝ)^2)) :
    (↑(Finset.range (cycleLength p)) : Set ℕ).PairwiseDisjoint
      (fun j => (fun z => fastOrbit h p δ z j) '' expandingSeed h p δ) := by
  have hl {i j : ℕ} (hij : i < j) (hjp : j < cycleLength p) :
      Disjoint ((fun z => fastOrbit h p δ z i) '' expandingSeed h p δ)
        ((fun z => fastOrbit h p δ z j) '' expandingSeed h p δ) := by
    rw [Set.disjoint_left]
    intro w hw₁ hw₂
    obtain ⟨x,hx,hex⟩ := hw₁
    obtain ⟨y,hy,hey⟩ := hw₂
    let k := j-i
    have he : k+i = j := by dsimp [k]; omega
    change fastOrbit h p δ y j = w at hey
    rw [← he,fastOrbit_add] at hey
    let e := trajectoryEquiv (asymmetricForce h p δ) (measurable_asymmetricForce h p δ) h i
    have hm : x = fastOrbit h p δ y k := e.injective (hex.trans hey.symm)
    rw [hm] at hx
    exact seed_has_no_second_crossing hh hp hδ hδp hy (by omega : 0 < k)
      (by omega : k < cycleLength p) hx
  intro i hi j hj hne
  simp only [Finset.mem_coe,Finset.mem_range] at hi hj
  rcases lt_or_gt_of_ne hne with hij | hji
  · exact hl hij hj
  · exact (hl hji hi).symm

theorem expandingSet_volume {h : ℝ} (hh : 0 < h) {p : ℕ} (hp : 7 ≤ p) {δ : ℝ}
    (hδ : 0 < δ) (hδp : δ ≤ 1/(80*(p:ℝ)^2)) :
    ((volume : Measure ℝ).prod volume) (expandingSet h p δ) =
      ENNReal.ofReal (3*(cycleLength p:ℝ)*h/200) := by
  let μ : Measure (ℝ×ℝ) := (volume : Measure ℝ).prod volume
  unfold expandingSet
  rw [measure_biUnion_finset (expandingSet_images_disjoint hh hp hδ hδp)
    (fun j _ => fastOrbit_measurableSet_image h p δ j (measurableSet_expandingSeed h p δ))]
  have he (j : ℕ) : μ ((fun z => fastOrbit h p δ z j) '' expandingSeed h p δ) =
      ENNReal.ofReal (3*h/200) := by
    let e := trajectoryEquiv (asymmetricForce h p δ) (measurable_asymmetricForce h p δ) h j
    have hp' : MeasurePreserving e μ μ :=
      trajectory_measurePreserving _ (measurable_asymmetricForce h p δ) _ _
    rw [← expandingSeed_volume hh p δ]
    change μ (e '' expandingSeed h p δ) = μ (expandingSeed h p δ)
    calc
      _ = (μ.map e) (e '' expandingSeed h p δ) := by rw [hp'.map_eq]
      _ = _ := by rw [e.measurableEmbedding.map_apply, Set.preimage_image_eq _ e.injective]
  simp_rw [show (volume : Measure ℝ).prod volume = μ from rfl,he]
  rw [Finset.sum_const,Finset.card_range,nsmul_eq_mul,← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

end BreakingResonance

#print axioms BreakingResonance.expandingSeed_volume
#print axioms BreakingResonance.expandingSet_images_disjoint
#print axioms BreakingResonance.expandingSet_volume
