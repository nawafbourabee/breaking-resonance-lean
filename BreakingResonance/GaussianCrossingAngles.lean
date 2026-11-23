import BreakingResonance.GaussianVerletMode
import Mathlib.Analysis.SpecialFunctions.PolarCoord

noncomputable section

open Real Set MeasureTheory
open scoped ENNReal

namespace BreakingResonance

def crossingAngleWindow (t : ℝ) : Set ℝ :=
  Ico (Real.pi/2) (min Real.pi (t+Real.pi/2)) ∪
    Ioo (-Real.pi) (max (-Real.pi) (t-3*Real.pi/2))

theorem crossingAngleWindow_measurable (t : ℝ) : MeasurableSet (crossingAngleWindow t) :=
  measurableSet_Ico.union measurableSet_Ioo

theorem crossingAngleWindow_volume {t : ℝ} :
    volume (crossingAngleWindow t) ≤ ENNReal.ofReal t := by
  have hp := Real.pi_pos
  unfold crossingAngleWindow
  refine (measure_union_le _ _).trans ?_
  rw [Real.volume_Ico,Real.volume_Ioo]
  by_cases hs : t ≤ Real.pi/2
  · have ha : t+Real.pi/2 ≤ Real.pi := by linarith only [hs]
    have hb : t-3*Real.pi/2 ≤ -Real.pi := by linarith only [hs]
    rw [min_eq_right ha,max_eq_left hb,sub_self,ENNReal.ofReal_zero,add_zero]
    apply ENNReal.ofReal_le_ofReal
    linarith
  · have ha : Real.pi ≤ t+Real.pi/2 := by linarith only [le_of_not_ge hs]
    have hb : -Real.pi ≤ t-3*Real.pi/2 := by linarith only [le_of_not_ge hs]
    rw [min_eq_left ha,max_eq_right hb,← ENNReal.ofReal_add (by linarith only [hp])
      (sub_nonneg.mpr hb)]
    apply ENNReal.ofReal_le_ofReal
    linarith

theorem crossingAngle_mem_window {t φ : ℝ} (ht : 0 ≤ t)
    (hφ : φ ∈ Ioo (-Real.pi) Real.pi) (hleft : Real.cos φ ≤ 0)
    (hright : 0 < Real.cos (φ-t)) : φ ∈ crossingAngleWindow t := by
  have hπ := Real.pi_pos
  have hsplit : φ ≤ -(Real.pi/2) ∨ Real.pi/2 ≤ φ := by
    by_contra! hn
    exact (not_lt_of_ge hleft) (Real.cos_pos_of_mem_Ioo ⟨hn.1,hn.2⟩)
  rcases hsplit with hl | hr
  · apply Or.inr
    refine ⟨hφ.1,lt_of_lt_of_le ?_ (le_max_right _ _)⟩
    by_contra! hbad
    have hx := Real.cos_nonpos_of_pi_div_two_le_of_le
      (show Real.pi/2 ≤ φ-t+2*Real.pi by linarith only [hbad])
      (show φ-t+2*Real.pi ≤ Real.pi+Real.pi/2 by linarith only [hl,ht])
    rw [Real.cos_add_two_pi] at hx
    exact (not_lt_of_ge hx) hright
  · apply Or.inl
    refine ⟨hr,lt_min hφ.2 ?_⟩
    by_contra! hbad
    have hx := Real.cos_nonpos_of_pi_div_two_le_of_le
      (show Real.pi/2 ≤ φ-t by linarith only [hbad])
      (show φ-t ≤ Real.pi+Real.pi/2 by linarith only [ht,hφ.2,hπ])
    exact (not_lt_of_ge hx) hright

end BreakingResonance

#print axioms BreakingResonance.crossingAngleWindow_volume
#print axioms BreakingResonance.crossingAngle_mem_window
