import BreakingResonance.LowerProductDynamics
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

noncomputable section

open MeasureTheory Set PersistencePays
open scoped ENNReal

namespace BreakingResonance

variable {ι : Type*} [Fintype ι]

theorem tilt_map_through_equiv {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]
    {μ : Measure S} {ν : Measure T} (e : S ≃ᵐ T) (he : MeasurePreserving e μ ν) (f : T → ℝ) :
    (μ.tilted (f ∘ e)).map e = ν.tilted f := by
  ext A hA
  rw [e.map_apply,tilted_apply_eq_ofReal_integral' (f ∘ e) (e.measurable hA),
    tilted_apply_eq_ofReal_integral' f hA]
  have he₁ := he.integral_comp e.measurableEmbedding (fun y => Real.exp (f y))
  rw [show (∫ x, Real.exp ((f ∘ e) x) ∂μ) = _ from he₁]
  congr 1
  exact he.setIntegral_preimage_emb e.measurableEmbedding (fun y =>
    Real.exp (f y)/(∫ x, Real.exp (f x) ∂ν)) A

/-- A sum of one-coordinate log densities tilts the product measure by
tilting its factors separately. -/
theorem pi_tilted_sum {S : Type*} [MeasurableSpace S] (μ : ι → Measure S)
    [∀ i, SigmaFinite (μ i)] (f : ι → S → ℝ) :
    (Measure.pi μ).tilted (fun x => ∑ i, f i (x i)) =
      Measure.pi (fun i => (μ i).tilted (f i)) := by
  apply (Measure.pi_eq (μ := fun i => (μ i).tilted (f i)) ?_).symm
  intro A hA
  rw [tilted_apply_eq_ofReal_integral' _ (MeasurableSet.univ_pi hA)]
  let p (i : ι) (x : S) := Real.exp (f i x)/(∫ y, Real.exp (f i y) ∂(μ i))
  have hp (x : ι → S) : Real.exp (∑ i, f i (x i))/
      (∫ y, Real.exp (∑ i, f i (y i)) ∂(Measure.pi μ)) = ∏ i, p i (x i) := by
    simp_rw [Real.exp_sum]
    rw [integral_fintype_prod_eq_prod (fun i x => Real.exp (f i x)),Finset.prod_div_distrib]
  simp_rw [hp]
  rw [← integral_indicator (MeasurableSet.univ_pi hA)]
  have hI : (univ.pi A).indicator (fun x => ∏ i, p i (x i)) =
      fun x => ∏ i, (A i).indicator (p i) (x i) := by
    classical
    funext x
    by_cases hx : x ∈ univ.pi A
    · rw [indicator_of_mem hx]
      apply Finset.prod_congr rfl
      intro i _
      exact (indicator_of_mem (mem_univ_pi.mp hx i) _).symm
    · rw [indicator_of_notMem hx]
      obtain ⟨i,hi⟩ := not_forall.mp (mt mem_univ_pi.mpr hx)
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (indicator_of_notMem hi _)).symm
  rw [hI,integral_fintype_prod_eq_prod]
  have hpos (i : ι) : 0 ≤ ∫ x, (A i).indicator (p i) x ∂(μ i) := by
    apply integral_nonneg
    intro x
    by_cases hx : x ∈ A i
    · rw [indicator_of_mem hx]
      exact div_nonneg (Real.exp_nonneg _) (integral_nonneg (fun _ => Real.exp_nonneg _))
    · simp [indicator_of_notMem hx]
  rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => hpos i)]
  apply Finset.prod_congr rfl
  intro i _
  rw [integral_indicator (hA i),tilted_apply_eq_ofReal_integral' _ (hA i)]

def phaseCoordinates (ι : Type*) [Fintype ι] :
    (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) ≃ᵐ (ι → ℝ×ℝ) :=
  (((MeasurableEquiv.toLp 2 (ι → ℝ)).symm).prodCongr
    ((MeasurableEquiv.toLp 2 (ι → ℝ)).symm)).trans
      (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ ι).symm

theorem phaseCoordinates_apply (z : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) (i : ι) :
    phaseCoordinates ι z i = (z.1 i,z.2 i) := rfl

theorem phaseCoordinates_volume :
    MeasurePreserving (phaseCoordinates ι)
      ((volume : Measure (EuclideanSpace ℝ ι)).prod volume)
      (Measure.pi (fun _ : ι => (volume : Measure ℝ).prod volume)) := by
  exact ((PiLp.volume_preserving_ofLp ι).prod (PiLp.volume_preserving_ofLp ι)).trans
    ((measurePreserving_arrowProdEquivProdArrow ℝ ℝ ι (fun _ => volume)
      (fun _ => volume)).symm)

theorem separablePotential_gibbs_integrable (a b : ι → ℝ) (ha : ∀ i, 0 < a i)
    (hab : ∀ i, a i ≤ b i) :
    Integrable (fun x => Real.exp (-separablePotential a b x)) volume := by
  let e := (MeasurableEquiv.toLp 2 (ι → ℝ)).symm
  have hi : Integrable (fun x : ι → ℝ => ∏ i, Real.exp (-fastPotential (a i) (b i) (x i)))
      (Measure.pi (fun _ => volume)) :=
    Integrable.fintype_prod (fun i => fastPotential_gibbs_integrable (ha i) (hab i))
  have he : MeasurePreserving e (volume : Measure (EuclideanSpace ℝ ι))
      (Measure.pi (fun _ => volume)) := PiLp.volume_preserving_ofLp ι
  have h := (he.integrable_comp_emb e.measurableEmbedding).mpr hi
  convert h using 1
  funext x
  simp [separablePotential,← Finset.sum_neg_distrib,Real.exp_sum,e]

theorem separablePhaseGibbs_coordinates (a b : ι → ℝ) (ha : ∀ i, 0 < a i)
    (hab : ∀ i, a i ≤ b i) :
    (phaseGibbs (separablePotential a b)).map (phaseCoordinates ι) =
      Measure.pi (fun i => phaseGibbs (fastPotential (a i) (b i))) := by
  have hU : Measurable (separablePotential a b) := (continuous_iff_continuousAt.mpr
    (fun x => (separablePotential_gradient a b x).differentiableAt.continuousAt)).measurable
  have hs := phaseGibbs_eq_tilted _ hU (separablePotential_gibbs_integrable a b ha hab)
  let F (z : ι → ℝ×ℝ) := ∑ i, -phaseEnergy (fastPotential (a i) (b i)) (z i)
  have he : -(phaseEnergy (separablePotential a b)) = F ∘ phaseCoordinates ι := by
    funext z
    simp [F,separableEnergy,phaseCoordinates_apply,Finset.sum_neg_distrib]
  rw [hs,he,tilt_map_through_equiv _ phaseCoordinates_volume]
  calc
    _ = Measure.pi (fun i => ((volume : Measure ℝ).prod volume).tilted (-phaseEnergy (fastPotential (a i) (b i)))) :=
      pi_tilted_sum (fun _ : ι => (volume : Measure ℝ).prod volume)
        (fun i => -phaseEnergy (fastPotential (a i) (b i)))
    _ = _ := by
      congr 1
      funext i
      exact (phaseGibbs_eq_tilted _ (fastPotential_continuous _ _).measurable
        (fastPotential_gibbs_integrable (ha i) (hab i))).symm

end BreakingResonance

#print axioms BreakingResonance.pi_tilted_sum
#print axioms BreakingResonance.phaseCoordinates_volume
#print axioms BreakingResonance.separablePhaseGibbs_coordinates
