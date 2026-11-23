import PersistencePays.ConditionalLawEntropy
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Tactic

/-! Relative entropy under a binary partition, including zero mass on either part. -/
noncomputable section
namespace BreakingResonance
open PersistencePays MeasureTheory ProbabilityTheory InformationTheory Set
open scoped ENNReal
variable {S : Type*} [MeasurableSpace S]

theorem restricted_klFun_jensen (μ ν : Measure S)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hK : klDiv μ ν ≠ ∞) (A : Set S) (hA : MeasurableSet A)
    (hp : 0 < ν.real A) :
    ν.real A * klFun (μ.real A / ν.real A) ≤
      ∫x in A,klFun ((μ.rnDeriv ν x).toReal) ∂ν := by
  have hac := (klDiv_ne_top_iff.mp hK).1
  have hi := (integrable_klFun_rnDeriv_iff hac).mpr (klDiv_ne_top_iff.mp hK).2
  have hne : ν.restrict A ≠ 0 := by
    intro hz
    have hh := congrArg (fun ξ : Measure S => ξ.real univ) hz
    apply (ne_of_gt hp)
    simpa [measureReal_def] using hh
  letI : NeZero (ν.restrict A) := ⟨hne⟩
  have hj := convexOn_klFun.map_average_le (μ:=ν.restrict A)
    (f:=fun x => (μ.rnDeriv ν x).toReal) continuous_klFun.continuousOn
    isClosed_Ici (Filter.Eventually.of_forall (fun x => ENNReal.toReal_nonneg))
    (Measure.integrable_toReal_rnDeriv (μ:=μ) (ν:=ν)).restrict hi.restrict
  simp only [average_eq,smul_eq_mul,measureReal_def,Measure.restrict_apply_univ] at hj
  rw [Measure.setIntegral_toReal_rnDeriv hac A] at hj
  change klFun ((ν.real A)⁻¹ * μ.real A) ≤
    (ν.real A)⁻¹ * (∫x in A,klFun ((μ.rnDeriv ν x).toReal) ∂ν) at hj
  have hm := mul_le_mul_of_nonneg_left hj hp.le
  simpa [div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc,ne_of_gt hp] using hm

theorem binary_partition_klFun (μ ν : Measure S)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hK : klDiv μ ν ≠ ∞) (A : Set S) (hA : MeasurableSet A)
    (hp : 0 < ν.real A) (hp' : ν.real A < 1) :
    ν.real A * klFun (μ.real A / ν.real A)+
      (1-ν.real A)*klFun ((1-μ.real A)/(1-ν.real A)) ≤
      (klDiv μ ν).toReal := by
  have hcν := probability_complement_toReal ν A hA
  have hcμ := probability_complement_toReal μ A hA
  change ν.real Aᶜ=1-ν.real A at hcν
  change μ.real Aᶜ=1-μ.real A at hcμ
  have hj := restricted_klFun_jensen μ ν hK A hA hp
  have hj' := restricted_klFun_jensen μ ν hK Aᶜ hA.compl
    (show 0 < ν.real Aᶜ by rw [hcν]; linarith)
  have hac := (klDiv_ne_top_iff.mp hK).1
  have hi := (integrable_klFun_rnDeriv_iff hac).mpr (klDiv_ne_top_iff.mp hK).2
  have he := integral_add_compl hA hi
  rw [←toReal_klDiv_eq_integral_klFun hac] at he
  rw [hcν,hcμ] at hj'
  linarith

theorem weighted_klFun_identity {x y : ℝ} (hy : 0<y) :
    y*klFun (x/y)=x*Real.log x-x*Real.log y+y-x := by
  by_cases hx : x=0
  · simp [hx,klFun]
  rw [klFun,Real.log_div hx hy.ne']
  field_simp

theorem binary_partition_entropy (μ ν : Measure S)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hK : klDiv μ ν ≠ ∞) (A : Set S) (hA : MeasurableSet A)
    (hp : 0 < ν.real A) (hp' : ν.real A < 1) :
    (1-μ.real Aᶜ)*Real.log (1/ν.real A)+
      μ.real Aᶜ*Real.log (1/(1-ν.real A))-Real.binEntropy (μ.real Aᶜ) ≤
      (klDiv μ ν).toReal := by
  have hj := binary_partition_klFun μ ν hK A hA hp hp'
  rw [weighted_klFun_identity hp,weighted_klFun_identity (by linarith : 0<1-ν.real A)] at hj
  have hcμ := probability_complement_toReal μ A hA
  change μ.real Aᶜ=1-μ.real A at hcμ
  rw [hcμ]
  simp only [Real.binEntropy,Real.log_inv,one_div]
  ring_nf at hj ⊢
  exact hj

end BreakingResonance
