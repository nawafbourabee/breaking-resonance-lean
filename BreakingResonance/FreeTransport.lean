import PersistencePays.NoOvershoot

/-! The actual free-transport entropy inequality on [0,h].

The entropy theorem is reused from Persistence Pays. The rescaling construction
below also follows PersistencePays.TimeScaledEntropy, with the joint law,
position marginal, and product reference all explicitly mapped. This is
verification of a reused ingredient, not a novelty claim. -/
namespace BreakingResonance
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory PersistencePays
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem freeTransport_unitInterval (μ : Measure (E × E)) [IsProbabilityMeasure μ]
    (e : E ≃L[ℝ] E) (b : E) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    conditionalGaussianEntropy μ
      ((ProbabilityTheory.stdGaussian E).map (fun x => e x + b)) t ≤
    conditionalGaussianEntropy μ
      ((ProbabilityTheory.stdGaussian E).map (fun x => e x + b)) 0 +
    conditionalGaussianEntropy μ
      ((ProbabilityTheory.stdGaussian E).map (fun x => e x + b)) 1 :=
  proposition_3_1_affine_law μ e b ht ht1

def scalarEquiv (h : ℝ) (hh : h ≠ 0) : E ≃L[ℝ] E :=
  (LinearEquiv.smulOfNeZero ℝ E h hh).toContinuousLinearEquiv

omit [MeasurableSpace E] [BorelSpace E] in
@[simp] lemma scalarEquiv_apply (h : ℝ) (hh : h ≠ 0) (x : E) :
    scalarEquiv h hh x = h • x := rfl

def velocityScale (h : ℝ) (hh : h ≠ 0) : (E × E) ≃ᵐ (E × E) where
  toFun := fun z => (z.1, h • z.2)
  invFun := fun z => (z.1, h⁻¹ • z.2)
  left_inv := by intro z; simp [smul_smul, hh]
  right_inv := by intro z; simp [smul_smul, hh]
  measurable_toFun := measurable_fst.prodMk (measurable_snd.const_smul h)
  measurable_invFun := measurable_fst.prodMk (measurable_snd.const_smul h⁻¹)

lemma transportJoint_scale (μ : Measure (E × E))
    (h : ℝ) (hh : h ≠ 0) (t : ℝ) :
    transportJoint (μ.map (velocityScale h hh)) t =
      (transportJoint μ (h*t)).map (velocityScale h hh) := by
  unfold transportJoint
  rw [Measure.map_map (measurable_freeTransport _) (velocityScale h hh).measurable,
    Measure.map_map (velocityScale h hh).measurable (measurable_freeTransport _)]
  congr 1
  funext z
  simp [velocityScale, freeTransport, drift, smul_smul, mul_comm]

lemma transportPosition_scale (μ : Measure (E × E))
    (h : ℝ) (hh : h ≠ 0) (t : ℝ) :
    transportPosition (μ.map (velocityScale h hh)) t =
      transportPosition μ (h*t) := by
  unfold transportPosition
  rw [transportJoint_scale]
  change (Measure.map (fun z : E × E => (z.1, h • z.2))
    (transportJoint μ (h*t))).fst = _
  have hm : Measurable (fun z : E × E => h • z.2) := measurable_snd.const_smul h
  rw [Measure.fst_map_prodMk hm]
  rfl

/-- The reference product is scaled in the velocity coordinate too. -/
lemma product_reference_scale (ν γ : Measure E) [SFinite ν] [SFinite γ]
    (h : ℝ) (hh : h ≠ 0) :
    ν.prod (γ.map (scalarEquiv (E := E) h hh)) =
      (ν.prod γ).map (velocityScale h hh) := by
  have hm := Measure.map_prod_map ν γ measurable_id
    (scalarEquiv h hh).continuous.measurable
  rw [Measure.map_id] at hm
  exact hm

/-- Actual KL invariance, with both probability measures mapped. -/
lemma conditionalGaussianEntropy_scale
    (μ : Measure (E × E)) [IsProbabilityMeasure μ]
    (γ : Measure E) [IsProbabilityMeasure γ]
    (h : ℝ) (hh : h ≠ 0) (t : ℝ) :
    conditionalGaussianEntropy (μ.map (velocityScale h hh))
      (γ.map (scalarEquiv (E := E) h hh)) t =
      conditionalGaussianEntropy μ γ (h*t) := by
  unfold conditionalGaussianEntropy
  rw [transportJoint_scale, transportPosition_scale, product_reference_scale]
  exact klDiv_map_measurableEquiv (velocityScale h hh)
    (transportJoint μ (h*t)) ((transportPosition μ (h*t)).prod γ)

/-- The manuscript's free-transport endpoint inequality on any positive
physical interval. Infinite endpoint entropies are allowed. -/
theorem freeTransport_interval (μ : Measure (E × E)) [IsProbabilityMeasure μ]
    {h t : ℝ} (hh : 0 < h) (ht : 0 ≤ t) (hth : t ≤ h) :
    conditionalGaussianEntropy μ (stdGaussian E) t ≤
      conditionalGaussianEntropy μ (stdGaussian E) 0 +
        conditionalGaussianEntropy μ (stdGaussian E) h := by
  have hne := ne_of_gt hh
  let μ' := μ.map (velocityScale h hne)
  let : IsProbabilityMeasure μ' :=
    Measure.isProbabilityMeasure_map (velocityScale h hne).measurable.aemeasurable
  have hb := proposition_3_1_affine_law μ' (scalarEquiv (E := E) h hne) 0
    (div_nonneg ht hh.le) ((div_le_one hh).mpr hth)
  simp only [add_zero] at hb
  change conditionalGaussianEntropy (μ.map (velocityScale h hne))
      ((stdGaussian E).map (scalarEquiv h hne)) (t/h) ≤
    conditionalGaussianEntropy (μ.map (velocityScale h hne))
      ((stdGaussian E).map (scalarEquiv h hne)) 0 +
    conditionalGaussianEntropy (μ.map (velocityScale h hne))
      ((stdGaussian E).map (scalarEquiv h hne)) 1 at hb
  simp only [conditionalGaussianEntropy_scale, mul_zero, mul_one] at hb
  have hc : h * (t/h) = t := by field_simp
  rwa [hc] at hb

/-- The same theorem with all laws expanded as pushforwards and actual KL. -/
theorem freeTransport_interval_kl (μ : Measure (E × E)) [IsProbabilityMeasure μ]
    {h t : ℝ} (hh : 0 < h) (ht : 0 ≤ t) (hth : t ≤ h) :
    klDiv (μ.map (fun z : E × E => (z.1 + t • z.2, z.2)))
      ((μ.map (fun z : E × E => z.1 + t • z.2)).prod (stdGaussian E)) ≤
    klDiv μ (μ.fst.prod (stdGaussian E)) +
      klDiv (μ.map (fun z : E × E => (z.1 + h • z.2, z.2)))
        ((μ.map (fun z : E × E => z.1 + h • z.2)).prod (stdGaussian E)) := by
  have hp (s : ℝ) : transportPosition μ s =
      μ.map (fun z : E × E => z.1 + s • z.2) := by
    unfold transportPosition transportJoint freeTransport drift
    rw [Measure.fst_map_prodMk measurable_snd]
  have hb := freeTransport_interval μ hh ht hth
  unfold conditionalGaussianEntropy at hb
  rw [transportJoint_zero, transportPosition_zero, hp t, hp h] at hb
  exact hb

/-- Finite endpoint entropies imply finite entropy at every intermediate time. -/
theorem freeTransport_interval_finite
    (μ : Measure (E × E)) [IsProbabilityMeasure μ] {h t : ℝ}
    (hh : 0 < h) (ht : 0 ≤ t) (hth : t ≤ h)
    (h0 : conditionalGaussianEntropy μ (stdGaussian E) 0 ≠ ∞)
    (h1 : conditionalGaussianEntropy μ (stdGaussian E) h ≠ ∞) :
    conditionalGaussianEntropy μ (stdGaussian E) t ≠ ∞ :=
  ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨h0, h1⟩)
    (freeTransport_interval μ hh ht hth)
end
end BreakingResonance

#print axioms BreakingResonance.freeTransport_interval
#print axioms BreakingResonance.freeTransport_interval_kl
#print axioms BreakingResonance.freeTransport_interval_finite
