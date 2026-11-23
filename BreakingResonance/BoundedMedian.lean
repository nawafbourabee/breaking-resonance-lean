import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section

open MeasureTheory Set

namespace BreakingResonance

variable {S : Type*} [MeasurableSpace S] (π : Measure S) [IsProbabilityMeasure π]

/-- A bounded measurable function has a median in its range interval,
with the two strict tails each having mass at most one half. -/
theorem exists_bounded_median {f : S → ℝ} (hf : Measurable f) {C : ℝ}
    (hlo : ∀ x, 0 ≤ f x) (hhi : ∀ x, f x ≤ C) :
    ∃ a ∈ Icc 0 C, π {x | f x < a} ≤ 1/2 ∧ π {x | a < f x} ≤ 1/2 := by
  let D : Set ℝ := {a | π {x | f x < a} ≤ 1/2}
  have hzero : 0 ∈ D := by
    have he : {x | f x < 0} = ∅ := by ext x; simp [not_lt.mpr (hlo x)]
    change π {x | f x < 0} ≤ 1/2
    rw [he, measure_empty]
    positivity
  have hhalf : (1/2 : ENNReal) < 1 := by
    norm_num
  have hupper : ∀ a ∈ D, a ≤ C := by
    intro a ha
    by_contra! h
    have he : {x | f x < a} = univ := by ext x; simp [(hhi x).trans_lt h]
    change π {x | f x < a} ≤ 1/2 at ha
    rw [he,measure_univ] at ha
    exact (not_le_of_gt hhalf) ha
  have hbdd : BddAbove D := ⟨C,hupper⟩
  let a := sSup D
  have hloD (t : ℝ) (ht : t < a) : t ∈ D := by
    obtain ⟨u,hu,htu⟩ := exists_lt_of_lt_csSup ⟨0,hzero⟩ ht
    exact (measure_mono (fun _ h => (show f _ < t from h).trans htu)).trans hu
  let u (n : ℕ) : ℝ := 1/((n:ℝ)+1)
  have hu (n : ℕ) : 0 < u n := by dsimp [u]; positivity
  have hu_mono : Antitone u := by
    intro n m hnm
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.succ_le_succ hnm)
  let A (n : ℕ) : Set S := {x | f x < a-u n}
  have hA : Monotone A := by
    intro i j hij x hx
    exact (show f x < a-u i from hx).trans_le (sub_le_sub_left (hu_mono hij) a)
  have hAu : (⋃ n, A n) = {x | f x < a} := by
    ext x
    rw [mem_iUnion]
    constructor
    · rintro ⟨n,hn⟩
      exact (show f x < a-u n from hn).trans (sub_lt_self a (hu n))
    · intro hx
      obtain ⟨n,hn⟩ := exists_nat_one_div_lt (sub_pos.mpr (show f x < a from hx))
      exact ⟨n, show f x < a-u n by dsimp [u]; linarith⟩
  have hleft : π {x | f x < a} ≤ 1/2 := by
    rw [← hAu,hA.measure_iUnion]
    exact iSup_le fun n => hloD (a-u n) (sub_lt_self a (hu n))
  let B (n : ℕ) : Set S := {x | f x < a+u n}
  have hB : Antitone B := by
    intro i j hij x hx
    exact (show f x < a+u j from hx).trans_le (add_le_add_right (hu_mono hij) a)
  have hBm (n : ℕ) : MeasurableSet (B n) := measurableSet_lt hf measurable_const
  have hBi : (⋂ n, B n) = {x | f x ≤ a} := by
    ext x
    rw [mem_iInter]
    constructor
    · intro hx
      change f x ≤ a
      by_contra! h
      obtain ⟨n,hn⟩ := exists_nat_one_div_lt (sub_pos.mpr h)
      have hxn : f x < a+u n := hx n
      dsimp [u] at hxn
      linarith
    · intro hx n
      exact (show f x ≤ a from hx).trans_lt (lt_add_of_pos_right a (hu n))
  have hright : (1/2 : ENNReal) ≤ π {x | f x ≤ a} := by
    rw [← hBi, hB.measure_iInter (fun n => (hBm n).nullMeasurableSet)
      ⟨0,measure_ne_top π (B 0)⟩]
    refine le_iInf fun n => le_of_lt ?_
    by_contra! h
    have hn : a+u n ∈ D := h
    exact (not_le_of_gt (lt_add_of_pos_right a (hu n))) (le_csSup hbdd hn)
  have hcomp : {x | a < f x} = {x | f x ≤ a}ᶜ := by ext x; simp
  refine ⟨a,⟨le_csSup hbdd hzero,csSup_le ⟨0,hzero⟩ hupper⟩,hleft,?_⟩
  rw [hcomp, measure_compl (measurableSet_le hf measurable_const) (measure_ne_top π _),
    measure_univ]
  exact (tsub_le_tsub_left hright _).trans (by norm_num)

end BreakingResonance

#print axioms BreakingResonance.exists_bounded_median
