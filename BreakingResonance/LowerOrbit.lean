import BreakingResonance.LowerCycleCoefficient

noncomputable section

open Matrix
open scoped Matrix Matrix.Norms.Operator

namespace BreakingResonance

def asymmetricForce (h : ℝ) (p : ℕ) (δ : ℝ) : ℝ → ℝ :=
  fastGradient (curvatureForAngle h (fastAngleNeg p δ))
    (curvatureForAngle h (fastAnglePos p δ))

def cycleLength (p : ℕ) : ℕ := 3*p

def cycleExpansion (p : ℕ) (δ : ℝ) : ℝ := 1+4/5*δ*cycleExpansionCoefficient p

theorem cycleExpansion_gt_one {p : ℕ} (hp : 7 ≤ p) {δ : ℝ} (hδ : 0 < δ) :
    1 < cycleExpansion p δ := by
  obtain ⟨_,hb,_⟩ := cycleExpansionCoefficient_bounds hp
  have hp₀ : 0 < (p:ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hb₀ : 0 < cycleExpansionCoefficient p := (by positivity : 0 < Real.pi/(8*(p:ℝ))).trans_le hb
  unfold cycleExpansion
  have h : 0 < 4/5*δ*cycleExpansionCoefficient p := by positivity
  linarith only [h]

theorem cycle_blocks {h : ℝ} (hh : 0 < h) {p : ℕ} (hp : 7 ≤ p) {δ : ℝ}
    (hδ : 0 < δ) (hδp : δ ≤ 1/(80*(p:ℝ)^2)) (z : ℝ×ℝ) (hz : returnCone z) :
    let a := fastAnglePos p δ
    let b := fastAngleNeg p δ
    let F := positionRecurrence (asymmetricForce h p δ) h
    let w := (harmonicStep a)^[p] z
    (∀ j ≤ p, F^[j] z = (harmonicStep a)^[j] z) ∧
    (∀ j ≤ 2*p, F^[p+j] z = (harmonicStep b)^[j] w) ∧
    (∀ j < p, z.1/2 ≤ (F^[j] z).1) ∧
    (∀ j < 2*p, (F^[p+j] z).1 ≤ -(z.1/2)) := by
  rcases z with ⟨x,y⟩
  let a := fastAnglePos p δ
  let b := fastAngleNeg p δ
  let F := positionRecurrence (asymmetricForce h p δ) h
  let w := (harmonicStep a)^[p] (x,y)
  obtain ⟨hx,_,hy⟩ := hz
  obtain ⟨hpos,hneg⟩ := lowerOrbit_signs hp hδ hδp hx hy
  have hA (j : ℕ) (hj : j ≤ p) : F^[j] (x,y) = (harmonicStep a)^[j] (x,y) := by
    apply iterate_agrees_on_prefix
    intro k hk
    have hk₁ := hpos k (hk.trans_le hj)
    change positionRecurrence (fastGradient (curvatureForAngle h b) (curvatureForAngle h a)) h _ = _
    rw [positionRecurrence_fast_theta h a b hh.ne',ite_eq_left (by linarith only [hk₁,hx])]
  have hB (j : ℕ) (hj : j ≤ 2*p) : F^[p+j] (x,y) = (harmonicStep b)^[j] w := by
    rw [Nat.add_comm,Function.iterate_add_apply,hA p le_rfl]
    apply iterate_agrees_on_prefix
    intro k hk
    have hk₁ := hneg k (hk.trans_le hj)
    change positionRecurrence (fastGradient (curvatureForAngle h b) (curvatureForAngle h a)) h _ = _
    rw [positionRecurrence_fast_theta h a b hh.ne',ite_eq_right (by linarith only [hk₁,hx])]
  exact ⟨hA,hB,fun j hj => by rw [hA j hj.le]; exact hpos j hj,
    fun j hj => by rw [hB j hj.le]; exact hneg j hj⟩

theorem cycle_step {h : ℝ} (hh : 0 < h) {p : ℕ} (hp : 7 ≤ p) {δ : ℝ}
    (hδ : 0 < δ) (hδp : δ ≤ 1/(80*(p:ℝ)^2)) (z : ℝ×ℝ) (hz : returnCone z) :
    let F := positionRecurrence (asymmetricForce h p δ) h
    let w := F^[cycleLength p] z
    returnCone w ∧ cycleExpansion p δ*z.1 ≤ w.1 := by
  let a := fastAnglePos p δ
  let b := fastAngleNeg p δ
  let F := positionRecurrence (asymmetricForce h p δ) h
  let β := Real.pi/(2*(p:ℝ))
  let t := δ*cycleExpansionCoefficient p
  obtain ⟨_,hB,_,_⟩ := cycle_blocks hh hp hδ hδp z hz
  obtain ⟨hc,hcoef,_⟩ := cycleExpansionCoefficient_bounds hp
  have hp₀ : 0 < (p:ℝ) := by exact_mod_cast (by omega : 0 < p)
  have ht : 0 < t := mul_pos hδ ((by positivity : 0 < Real.pi/(8*(p:ℝ))).trans_le hcoef)
  have hE := (cycleReturn_small_remainder hp hδ hδp).le
  have hr := expandedCone_of_small_remainder ht hc (Real.cos_le_one β)
    (cycleReturnMatrix_det p δ) hE hz
  have hcount : cycleLength p = p+2*p := by unfold cycleLength; omega
  have hmap : orbitVector (F^[cycleLength p] z) = cycleReturnMatrix p δ *ᵥ orbitVector z := by
    rw [hcount,hB _ le_rfl,harmonicMatrix_iterate,harmonicMatrix_iterate,Matrix.mulVec_mulVec]
    rfl
  have he : F^[cycleLength p] z = orbitPair (cycleReturnMatrix p δ *ᵥ orbitVector z) := by
    rw [← hmap,orbitPair_vector]
  change returnCone (F^[cycleLength p] z) ∧ cycleExpansion p δ*z.1 ≤ (F^[cycleLength p] z).1
  rw [he]
  refine ⟨hr.1,?_⟩
  change cycleExpansion p δ*z.1 ≤ (cycleReturnMatrix p δ *ᵥ orbitVector z) 0
  exact (show cycleExpansion p δ*z.1 = (1+4*t/5)*z.1 by
    dsimp [cycleExpansion,t]; ring).le.trans hr.2

/-- Lemma 7.1, applied for any number of full cycles of the actual scalar
position recurrence. The bounds within a cycle are in `cycle_blocks`. -/
theorem expandingVerletOrbit {h : ℝ} (hh : 0 < h) (hh₁ : h ≤ 1) {δ : ℝ}
    (hδ : 0 < δ) (hδp : δ ≤ 1/(80*(cycleHalfLength h:ℝ)^2))
    (z : ℝ×ℝ) (hz : returnCone z) (k : ℕ) :
    let p := cycleHalfLength h
    let F := positionRecurrence (asymmetricForce h p δ) h
    let w := F^[k*cycleLength p] z
    returnCone w ∧ (cycleExpansion p δ)^k*z.1 ≤ w.1 := by
  let p := cycleHalfLength h
  let F := positionRecurrence (asymmetricForce h p δ) h
  obtain ⟨hp,_,_⟩ := cycleHalfLength_bounds hh hh₁
  have hχ := (cycleExpansion_gt_one hp hδ).le
  change returnCone (F^[k*cycleLength p] z) ∧
    (cycleExpansion p δ)^k*z.1 ≤ (F^[k*cycleLength p] z).1
  induction k with
  | zero => simpa using hz
  | succ k ih =>
    rw [Nat.succ_mul,Nat.add_comm,Function.iterate_add_apply]
    have h := cycle_step hh hp hδ hδp _ ih.1
    refine ⟨h.1,?_⟩
    calc
      _ = cycleExpansion p δ*((cycleExpansion p δ)^k*z.1) := by rw [pow_succ]; ring
      _ ≤ cycleExpansion p δ*(F^[k*cycleLength p] z).1 :=
        mul_le_mul_of_nonneg_left ih.2 (zero_le_one.trans hχ)
      _ ≤ _ := h.2

end BreakingResonance

#print axioms BreakingResonance.cycle_blocks
#print axioms BreakingResonance.cycle_step
#print axioms BreakingResonance.expandingVerletOrbit
