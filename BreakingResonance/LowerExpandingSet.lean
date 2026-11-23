import BreakingResonance.LowerCycleEnergy

noncomputable section

open MeasureTheory Set PersistencePays

namespace BreakingResonance

/-- The initial crossing set E in Section 7.3. -/
def expandingSeed (h : ℝ) (p : ℕ) (δ : ℝ) : Set (ℝ×ℝ) :=
  {z | h/10 ≤ z.1 ∧ z.1 ≤ h/5 ∧ -4*z.1 ≤ Real.cos (fastAnglePos p δ)*z.1-h*z.2
    ∧ Real.cos (fastAnglePos p δ)*z.1-h*z.2 ≤ -3*z.1}

def expandingSet (h : ℝ) (p : ℕ) (δ : ℝ) : Set (ℝ×ℝ) :=
  ⋃ j ∈ Finset.range (cycleLength p), (fun z => fastOrbit h p δ z j) '' expandingSeed h p δ

theorem measurableSet_expandingSeed (h : ℝ) (p : ℕ) (δ : ℝ) :
    MeasurableSet (expandingSeed h p δ) := by
  let a := Real.cos (fastAnglePos p δ)
  have h₁ : Measurable (fun z : ℝ×ℝ => a*z.1-h*z.2) := by fun_prop
  have h₂ : Measurable (fun z : ℝ×ℝ => -4*z.1) := by fun_prop
  have h₃ : Measurable (fun z : ℝ×ℝ => -3*z.1) := by fun_prop
  exact ((measurableSet_le measurable_const measurable_fst).inter
    ((measurableSet_le measurable_fst measurable_const).inter
       ((measurableSet_le h₂ h₁).inter (measurableSet_le h₁ h₃))))

theorem seed_pair_in_cone {h : ℝ} (hh : 0 < h) {p : ℕ} {δ : ℝ} {z : ℝ×ℝ}
    (hz : z ∈ expandingSeed h p δ) :
    returnCone (fastPositionPair h p δ z) := by
  obtain ⟨hlo,_,hl,hu⟩ := hz
  have hx : 0 < z.1 := (by positivity : 0 < h/10).trans_le hlo
  have he := (fast_energy_coordinates hh.ne' (fastAnglePos p δ) (fastAngleNeg p δ) z).1
  change fastPositionPair h p δ z =
    (z.1,Real.cos (if 0 ≤ z.1 then fastAnglePos p δ else fastAngleNeg p δ)*z.1-h*z.2) at he
  rw [ite_eq_left hx.le] at he
  rw [he]
  exact ⟨hx,hl,hu⟩

theorem seed_quadratic_upper {h : ℝ} (hh : 0 < h) (hh₁ : h ≤ 1) {δ : ℝ}
    (hδ : 0 < δ) (hδp : δ ≤ 1/(80*(cycleHalfLength h:ℝ)^2))
    {z : ℝ×ℝ} (hz : z ∈ expandingSeed h (cycleHalfLength h) δ) :
    let p := cycleHalfLength h
    orbitQuadratic h (fastAnglePos p δ) (fastPositionPair h p δ z) ≤ 26/25 := by
  let p := cycleHalfLength h
  let a := fastAnglePos p δ
  let b := fastAngleNeg p δ
  let curv := curvatureForAngle h a
  obtain ⟨hlo,hhi,hl,hu⟩ := hz
  have hx : 0 < z.1 := (by positivity : 0 < h/10).trans_le hlo
  obtain ⟨hp,_,_⟩ := cycleHalfLength_bounds hh hh₁
  obtain ⟨hb,_,hba,ha,_,_,_⟩ := fastAngle_bounds hp hδ hδp
  have ha₀ : 0 ≤ a := hb.le.trans hba.le
  have hcos₀ : 0 ≤ Real.cos a := (Real.cos_pos_of_mem_Ioo
    ⟨by linarith only [ha₀,Real.pi_pos],by linarith only [ha,Real.pi_pos]⟩).le
  have hv₀ : 0 ≤ z.2 := by
    apply nonneg_of_mul_nonneg_right _ hh
    nlinarith only [hu,mul_nonneg hcos₀ hx.le,hx]
  have hv₁ : z.2 ≤ 1 := by
    apply le_of_mul_le_mul_left _ hh
    have hc := mul_le_mul_of_nonneg_right (Real.cos_le_one a) hx.le
    nlinarith only [hc,hl,hhi]
  have hv₂ : z.2^2 ≤ 1 := by simpa using (sq_le_sq₀ hv₀ zero_le_one).mpr hv₁
  have hx₂ : z.1^2 ≤ (1/5:ℝ)^2 := (sq_le_sq₀ hx.le (by norm_num)).mpr (by linarith only [hhi,hh₁])
  obtain ⟨_,hc,_,_⟩ := fastCurvature_bounds hh hh₁ hδ hδp
  have hcurv : 0 ≤ curv := by unfold curv curvatureForAngle; positivity
  have hcoef : curv*(1-h^2*curv/4) ≤ 1 := by
    have h' : 0 ≤ h^2*curv/4 := by positivity
    have hmul := mul_le_mul_of_nonneg_left
      (show 1-h^2*curv/4 ≤ 1 by linarith only [h']) hcurv
    exact (hmul.trans_eq (mul_one curv)).trans hc.le
  have hQ := (fast_energy_coordinates hh.ne' a b z).2.2
  change orbitQuadratic h (if 0 ≤ z.1 then a else b) (fastPositionPair h p δ z) =
    z.2^2+curvatureForAngle h (if 0 ≤ z.1 then a else b)*
      (1-h^2*curvatureForAngle h (if 0 ≤ z.1 then a else b)/4)*z.1^2 at hQ
  rw [ite_eq_left hx.le] at hQ
  change orbitQuadratic h a (fastPositionPair h p δ z) ≤ 26/25
  rw [hQ]
  have hmul := mul_le_mul_of_nonneg_right hcoef (sq_nonneg z.1)
  linarith only [hv₂,hx₂,hmul]

theorem expandingSet_energy_upper {h : ℝ} (hh : 0 < h) (hh₁ : h ≤ 1) {δ : ℝ}
    (hδ : 0 < δ) (hδp : δ ≤ 1/(80*(cycleHalfLength h:ℝ)^2))
    {z : ℝ×ℝ} (hz : z ∈ expandingSet h (cycleHalfLength h) δ) :
    fastEnergy h (cycleHalfLength h) δ z < 2 := by
  simp only [expandingSet,mem_iUnion,Finset.mem_range,mem_image] at hz
  obtain ⟨j,hj,u,hu,rfl⟩ := hz
  have hb := (fastOrbit_energy_during_cycle hh hh₁ hδ hδp u (seed_pair_in_cone hh hu) j hj).2
  have hQ := seed_quadratic_upper hh hh₁ hδ hδp hu
  linarith only [hb,hQ]

set_option maxHeartbeats 800000 in
/-- The lower energy bound of Lemma 7.2 at every subsequent iterate. -/
theorem expandingSet_energy_lower {h : ℝ} (hh : 0 < h) (hh₁ : h ≤ 1) {δ : ℝ}
    (hδ : 0 < δ) (hδp : δ ≤ 1/(80*(cycleHalfLength h:ℝ)^2))
    {z : ℝ×ℝ} (hz : z ∈ expandingSet h (cycleHalfLength h) δ) (n : ℕ) :
    let p := cycleHalfLength h
    (cycleExpansion p δ)^(2*(n/cycleLength p))/20 ≤
      fastEnergy h p δ (fastOrbit h p δ z n) := by
  let p := cycleHalfLength h
  let a := fastAnglePos p δ
  let χ := cycleExpansion p δ
  let q := cycleLength p
  obtain ⟨hp,_,_⟩ := cycleHalfLength_bounds hh hh₁
  have hq : 0 < q := by unfold q cycleLength; omega
  obtain ⟨hb,_,hba,ha,_,_,_⟩ := fastAngle_bounds hp hδ hδp
  have ha₀ : 0 ≤ a := hb.le.trans hba.le
  have hcos₀ : 0 ≤ Real.cos a := (Real.cos_pos_of_mem_Ioo
    ⟨by linarith only [ha₀,Real.pi_pos],by linarith only [ha,Real.pi_pos]⟩).le
  have hχ := (cycleExpansion_gt_one hp hδ).le
  have hseed {u : ℝ×ℝ} (hu : u ∈ expandingSeed h p δ) (m : ℕ) :
      χ^(2*(m/q))/20 ≤ fastEnergy h p δ (fastOrbit h p δ u m) := by
    let k := m/q
    let j := m%q
    let v := fastOrbit h p δ u (k*q)
    have hcone := seed_pair_in_cone hh hu
    have hu₁ : h/10 ≤ u.1 := hu.1
    have hdiv : k*q+j = m := by
      dsimp [k,j]
      rw [Nat.add_comm,Nat.mul_comm]
      exact Nat.mod_add_div _ _
    have hj : j < q := Nat.mod_lt _ hq
    obtain ⟨hv,hgrow⟩ := expandingVerletOrbit hh hh₁ hδ hδp _ hcone k
    change returnCone ((positionRecurrence (asymmetricForce h p δ) h)^[k*q] (fastPositionPair h p δ u)) at hv
    change χ^k*u.1 ≤ ((positionRecurrence (asymmetricForce h p δ) h)^[k*q] (fastPositionPair h p δ u)).1 at hgrow
    rw [← fastOrbit_pair] at hv hgrow
    change returnCone (fastPositionPair h p δ v) at hv
    change χ^k*u.1 ≤ v.1 at hgrow
    have henergy := (fastOrbit_energy_during_cycle hh hh₁ hδ hδp v hv j hj).1
    change orbitQuadratic h a (fastPositionPair h p δ v)/2 ≤
      fastEnergy h p δ (fastOrbit h p δ v j) at henergy
    have hQ := orbitQuadratic_cone_lower (h := h) (a := a) hcos₀ hv
    change 10*(v.1/h)^2 ≤ _ at hQ
    have hfirst : χ^k/10 ≤ v.1/h := by
      apply (le_div_iff₀ hh).mpr
      have hmul := mul_le_mul_of_nonneg_left hu₁ (pow_nonneg (zero_le_one.trans hχ) k)
      linarith only [hmul,hgrow]
    have hχ₀ : 0 ≤ χ := zero_le_one.trans hχ
    have hv₀ : 0 ≤ v.1 := hv.1.le
    have hs := (sq_le_sq₀ (by positivity : 0 ≤ χ^k/10) (by positivity : 0 ≤ v.1/h)).mpr hfirst
    conv_rhs => rw [← hdiv,fastOrbit_add]
    change χ^(2*k)/20 ≤ fastEnergy h p δ (fastOrbit h p δ v j)
    rw [Nat.mul_comm,pow_mul]
    nlinarith only [hs,hQ,henergy]
  simp only [expandingSet,mem_iUnion,Finset.mem_range,mem_image] at hz
  obtain ⟨j,_,u,hu,rfl⟩ := hz
  change χ^(2*(n/q))/20 ≤ fastEnergy h p δ (fastOrbit h p δ (fastOrbit h p δ u j) n)
  rw [← fastOrbit_add]
  apply le_trans _ (hseed hu (j+n))
  apply div_le_div_of_nonneg_right _ (by norm_num)
  exact pow_le_pow_right₀ hχ (Nat.mul_le_mul_left 2 (Nat.div_le_div_right (by omega)))

end BreakingResonance

#print axioms BreakingResonance.measurableSet_expandingSeed
#print axioms BreakingResonance.seed_pair_in_cone
#print axioms BreakingResonance.seed_quadratic_upper
#print axioms BreakingResonance.expandingSet_energy_upper
#print axioms BreakingResonance.expandingSet_energy_lower
