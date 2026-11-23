import BreakingResonance.LowerOrbitEnergy

noncomputable section

open PersistencePays

namespace BreakingResonance

def fastEnergy (h : ℝ) (p : ℕ) (δ : ℝ) (z : ℝ×ℝ) : ℝ :=
  phaseEnergy (asymmetricPotential h p δ) z

def fastPositionPair (h : ℝ) (p : ℕ) (δ : ℝ) (z : ℝ×ℝ) : ℝ×ℝ :=
  consecutivePositions (asymmetricForce h p δ) h z

def fastOrbit (h : ℝ) (p : ℕ) (δ : ℝ) (z : ℝ×ℝ) (n : ℕ) : ℝ×ℝ :=
  trajectory (asymmetricForce h p δ) h z n

theorem fastOrbit_add (h : ℝ) (p : ℕ) (δ : ℝ) (z : ℝ×ℝ) (n j : ℕ) :
    fastOrbit h p δ z (n+j) = fastOrbit h p δ (fastOrbit h p δ z n) j := by
  unfold fastOrbit trajectory
  rw [Nat.add_comm,Function.iterate_add_apply]

theorem fastOrbit_pair (h : ℝ) (p : ℕ) (δ : ℝ) (z : ℝ×ℝ) (n : ℕ) :
    fastPositionPair h p δ (fastOrbit h p δ z n) =
      (positionRecurrence (asymmetricForce h p δ) h)^[n] (fastPositionPair h p δ z) :=
  consecutivePositions_iterate _ _ _ _

set_option maxHeartbeats 800000 in
/-- One cycle in Lemma 7.2. The quadratic form is constant on each block,
and it increases by at most a factor two at the intervening switch. -/
theorem fastOrbit_energy_during_cycle {h : ℝ} (hh : 0 < h) (hh₁ : h ≤ 1) {δ : ℝ}
    (hδ : 0 < δ) (hδp : δ ≤ 1/(80*(cycleHalfLength h:ℝ)^2))
    (z : ℝ×ℝ) (hz : returnCone (fastPositionPair h (cycleHalfLength h) δ z))
    (j : ℕ) (hj : j < cycleLength (cycleHalfLength h)) :
    let p := cycleHalfLength h
    let q₀ := orbitQuadratic h (fastAnglePos p δ) (fastPositionPair h p δ z)
    q₀/2 ≤ fastEnergy h p δ (fastOrbit h p δ z j) ∧
      fastEnergy h p δ (fastOrbit h p δ z j) ≤ 4*q₀/3 := by
  let p := cycleHalfLength h
  let a := fastAnglePos p δ
  let b := fastAngleNeg p δ
  let zz := fastPositionPair h p δ z
  let F := positionRecurrence (asymmetricForce h p δ) h
  let w := (harmonicStep a)^[p] zz
  let q₀ := orbitQuadratic h a zz
  obtain ⟨hp,_,_⟩ := cycleHalfLength_bounds hh hh₁
  obtain ⟨hb,_,hba,haπ,_,_,_⟩ := fastAngle_bounds hp hδ hδp
  obtain ⟨_,hcurva,hcurvb,hcurvba⟩ := fastCurvature_bounds hh hh₁ hδ hδp
  have hcurva₁ : h^2*curvatureForAngle h a ≤ 1 := by
    have hsq : h^2 ≤ 1 := by
      simpa using (sq_le_sq₀ hh.le zero_le_one).mpr hh₁
    simpa using mul_le_mul hsq hcurva.le
      (show 0 ≤ curvatureForAngle h a by unfold curvatureForAngle; positivity)
      (by norm_num : (0:ℝ) ≤ 1)
  have hcurvb₁ : h^2*curvatureForAngle h b ≤ 1 :=
    (mul_le_mul_of_nonneg_left hcurvba.le (sq_nonneg h)).trans hcurva₁
  have ha₀ : 0 ≤ a := hb.le.trans hba.le
  have hcosA : 0 ≤ Real.cos a := (Real.cos_pos_of_mem_Ioo
    ⟨by linarith only [ha₀,Real.pi_pos],by linarith only [haπ,Real.pi_pos]⟩).le
  have hcosAB : Real.cos a ≤ Real.cos b := Real.strictAntiOn_cos.antitoneOn
    ⟨hb.le,by linarith only [hba,haπ,Real.pi_pos]⟩
    ⟨ha₀,by linarith only [haπ,Real.pi_pos]⟩ hba.le
  obtain ⟨hA,hB,hpos,hneg⟩ := cycle_blocks hh hp hδ hδp zz hz
  have hp₀ : 0 < p := by omega
  have hwn : w.1 ≤ -(zz.1/2) := by
    have he := hneg 0 (by omega : 0 < 2*p)
    change (F^[p+0] zz).1 ≤ -(zz.1/2) at he
    rw [add_zero,hA p le_rfl] at he
    exact he
  have hwp : zz.1/2 ≤ w.2 := by
    have he := hpos (p-1) (by omega : p-1 < p)
    rw [hA _ (by omega)] at he
    have heq : p = (p-1)+1 := by omega
    change zz.1/2 ≤ (((harmonicStep a)^[p] zz).2)
    conv_rhs => rw [heq,Function.iterate_succ_apply']
    exact he
  have hzhalf : 0 ≤ zz.1/2 := div_nonneg hz.1.le (by norm_num)
  have hcross : w.1*w.2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg
    (hwn.trans (neg_nonpos.mpr hzhalf)) (hzhalf.trans hwp)
  obtain ⟨hQlo,hQhi⟩ := orbitQuadratic_switch (h := h) hcosA hcosAB hcross
  rw [orbitQuadratic_iterate] at hQlo hQhi
  have hq₀ : 0 ≤ q₀ := by
    have hq := orbitQuadratic_cone_lower (h := h) (a := a) hcosA hz
    exact (by positivity : 0 ≤ 10*(zz.1/h)^2).trans hq
  let zj := fastOrbit h p δ z j
  have hpair : fastPositionPair h p δ zj = F^[j] zz := fastOrbit_pair h p δ z j
  obtain ⟨hlow,hup⟩ := fast_energy_sandwich hh.ne' a b zj hcurva₁ hcurvb₁
  change orbitQuadratic h (if 0 ≤ zj.1 then a else b) (fastPositionPair h p δ zj)/2 ≤
    fastEnergy h p δ zj at hlow
  change fastEnergy h p δ zj ≤ orbitQuadratic h (if 0 ≤ zj.1 then a else b)
    (fastPositionPair h p δ zj)/(2*(1-h^2*curvatureForAngle h (if 0 ≤ zj.1 then a else b)/4)) at hup
  change q₀/2 ≤ fastEnergy h p δ zj ∧ fastEnergy h p δ zj ≤ 4*q₀/3
  by_cases hjp : j < p
  · have hzj : 0 ≤ zj.1 := by
      have hm := hpos j hjp
      change zz.1/2 ≤ (F^[j] zz).1 at hm
      rw [← hpair] at hm
      exact hzhalf.trans hm
    have he : orbitQuadratic h a (fastPositionPair h p δ zj) = q₀ := by
      rw [hpair,hA j hjp.le,orbitQuadratic_iterate]
    rw [ite_eq_left hzj,he] at hlow hup
    have hscaled := (le_div_iff₀ (show 0 < 2*(1-h^2*curvatureForAngle h a/4) by
      linarith only [hcurva₁])).mp hup
    have hH : 0 ≤ fastEnergy h p δ zj := by linarith only [hlow,hq₀]
    have hm := mul_le_mul_of_nonneg_left
      (show 3/2 ≤ 2*(1-h^2*curvatureForAngle h a/4) by linarith only [hcurva₁]) hH
    exact ⟨hlow, by linarith only [hm,hscaled,hq₀]⟩
  · let k := j-p
    have hk : k < 2*p := by unfold cycleLength at hj; dsimp [k]; omega
    have hjk : p+k = j := Nat.add_sub_of_le (le_of_not_gt hjp)
    have hzj : ¬ 0 ≤ zj.1 := by
      have h := hneg k hk
      rw [hjk,← hpair] at h
      have hh' : 0 < zz.1 := hz.1
      exact not_le.mpr (by change zj.1 < 0; change zj.1 ≤ -(zz.1/2) at h; linarith only [h,hh'])
    have he : orbitQuadratic h b (fastPositionPair h p δ zj) = orbitQuadratic h b w := by
      rw [hpair,← hjk,hB k hk.le,orbitQuadratic_iterate]
    rw [ite_eq_right hzj,he] at hlow hup
    have hscaled := (le_div_iff₀ (show 0 < 2*(1-h^2*curvatureForAngle h b/4) by
      linarith only [hcurvb₁])).mp hup
    have hH : 0 ≤ fastEnergy h p δ zj := by linarith only [hlow,hQlo,hq₀]
    have hm := mul_le_mul_of_nonneg_left
      (show 3/2 ≤ 2*(1-h^2*curvatureForAngle h b/4) by linarith only [hcurvb₁]) hH
    exact ⟨by linarith only [hlow,hQlo], by linarith only [hm,hscaled,hQhi]⟩

end BreakingResonance

#print axioms BreakingResonance.fastOrbit_add
#print axioms BreakingResonance.fastOrbit_pair
#print axioms BreakingResonance.fastOrbit_energy_during_cycle
