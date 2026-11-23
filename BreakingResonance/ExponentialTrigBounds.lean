import BreakingResonance.ExponentialBernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! Elementary analytic bounds used by the exponential duration comparison. -/
noncomputable section
namespace BreakingResonance
open Set

private theorem nonneg_from_derivative_on_Icc {F D : ℝ → ℝ} {x : ℝ} (hx : 0 ≤ x)
    (hF : ∀ t, HasDerivAt F (D t) t) (hF₀ : F 0 = 0)
    (hD : ∀ t ∈ Icc 0 x, 0 ≤ D t) :
    0 ≤ F x := by
  have hm : MonotoneOn F (Icc 0 x) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
      (fun t _ => (hF t).continuousAt.continuousWithinAt)
      (fun t _ => (hF t).differentiableAt.differentiableWithinAt)
    intro t ht
    rw [(hF t).deriv]
    exact hD t (interior_subset ht)
  have he := hm (show 0 ∈ Icc (0:ℝ) x from ⟨le_rfl,hx⟩)
    (show x ∈ Icc (0:ℝ) x from ⟨hx,le_rfl⟩) hx
  exact hF₀ ▸ he

theorem cosine_le_degree_four (x : ℝ) (hx : 0 ≤ x) :
    Real.cos x ≤ 1-x^2/2+x^4/24 := by
  apply sub_nonneg.mp
  let F := fun x : ℝ => 1-x^2/2+x^4/24-Real.cos x
  have hf (t : ℝ) : HasDerivAt F (Real.sin t-(t-t^3/6)) t := by
    unfold F
    convert
      (((hasDerivAt_const t (1:ℝ)).sub
        (((hasDerivAt_id t).pow 2).div_const 2)).add
        (((hasDerivAt_id t).pow 4).div_const 24)).sub (Real.hasDerivAt_cos t)
      using 1 <;> first | rfl | (try simp only [id_eq, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply]); ring
  exact nonneg_from_derivative_on_Icc (F := F) hx hf (by simp [F])
    (fun t ht => sub_nonneg.mpr (Real.sin_ge_sub_cube ht.1))

theorem sine_le_degree_five (x : ℝ) (hx : 0 ≤ x) :
    Real.sin x ≤ x-x^3/6+x^5/120 := by
  apply sub_nonneg.mp
  let F := fun x : ℝ => x-x^3/6+x^5/120-Real.sin x
  have hf (t : ℝ) : HasDerivAt F (1-t^2/2+t^4/24-Real.cos t) t := by
    unfold F
    convert
      ((((hasDerivAt_id t).sub (((hasDerivAt_id t).pow 3).div_const 6)).add
        (((hasDerivAt_id t).pow 5).div_const 120)).sub (Real.hasDerivAt_sin t))
      using 1 <;> first | rfl | (try simp only [id_eq, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply]); ring
  exact nonneg_from_derivative_on_Icc (F := F) hx hf (by simp [F])
    (fun t ht => sub_nonneg.mpr (cosine_le_degree_four t ht.1))

theorem cosine_ge_degree_six (x : ℝ) (hx : 0 ≤ x) :
    1-x^2/2+x^4/24-x^6/720 ≤ Real.cos x := by
  apply sub_nonneg.mp
  let F := fun x : ℝ => Real.cos x-(1-x^2/2+x^4/24-x^6/720)
  have hf (t : ℝ) : HasDerivAt F (t-t^3/6+t^5/120-Real.sin t) t := by
    unfold F
    convert
      (Real.hasDerivAt_cos t).sub
        ((((hasDerivAt_const t (1:ℝ)).sub (((hasDerivAt_id t).pow 2).div_const 2)).add
          (((hasDerivAt_id t).pow 4).div_const 24)).sub (((hasDerivAt_id t).pow 6).div_const 720))
      using 1 <;> first | rfl | (try simp only [id_eq, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply]); ring
  exact nonneg_from_derivative_on_Icc (F := F) hx hf (by simp [F])
    (fun t ht => sub_nonneg.mpr (sine_le_degree_five t ht.1))

theorem sine_ge_degree_seven (x : ℝ) (hx : 0 ≤ x) :
    x-x^3/6+x^5/120-x^7/5040 ≤ Real.sin x := by
  apply sub_nonneg.mp
  let F := fun x : ℝ => Real.sin x-(x-x^3/6+x^5/120-x^7/5040)
  have hf (t : ℝ) : HasDerivAt F (Real.cos t-(1-t^2/2+t^4/24-t^6/720)) t := by
    unfold F
    convert
      (Real.hasDerivAt_sin t).sub
        ((((hasDerivAt_id t).sub (((hasDerivAt_id t).pow 3).div_const 6)).add
          (((hasDerivAt_id t).pow 5).div_const 120)).sub (((hasDerivAt_id t).pow 7).div_const 5040))
      using 1 <;> first | rfl | (try simp only [id_eq, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply]); ring
  exact nonneg_from_derivative_on_Icc (F := F) hx hf (by simp [F])
    (fun t ht => sub_nonneg.mpr (cosine_ge_degree_six t ht.1))

theorem arctan_ge_degree_three (x : ℝ) (hx : 0 ≤ x) :
    x-x^3/3 ≤ Real.arctan x := by
  apply sub_nonneg.mp
  let F := fun x : ℝ => Real.arctan x-(x-x^3/3)
  have hf (t : ℝ) : HasDerivAt F (t^4/(1+t^2)) t := by
    unfold F
    have hp : HasDerivAt (fun x : ℝ => x-x^3/3) (1-t^2) t := by
      convert (hasDerivAt_id t).sub (((hasDerivAt_id t).pow 3).div_const 3) using 1 <;> first | rfl | (try simp only [id_eq, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply]); ring
    have hpos : 0 < 1+t^2 := by positivity
    have he : (1/(1+t^2)) - (1-t^2) = t^4/(1+t^2) := by
      field_simp [hpos.ne']
      ring
    rw [← he]
    exact (Real.hasDerivAt_arctan t).sub hp
  exact nonneg_from_derivative_on_Icc (F := F) hx hf (by simp [F]) (fun t _ => by positivity)

theorem exponential_half_ratio_le (u : ℝ) (hu : 0 ≤ u) :
    (1-Real.exp (-u))/(1+Real.exp (-u)) ≤ u/2 := by
  let F := fun u : ℝ => u*(1+Real.exp (-u))-2*(1-Real.exp (-u))
  have hf (t : ℝ) : HasDerivAt F (1-(1+t)*Real.exp (-t)) t := by
    have he : HasDerivAt (fun x : ℝ => Real.exp (-x)) (-Real.exp (-t)) t := by
      convert (Real.hasDerivAt_exp (-t)).comp t ((hasDerivAt_id t).neg) using 1
      all_goals first | rfl | (try simp only [id_eq, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply]); ring
    unfold F
    convert
      ((hasDerivAt_id t).mul ((hasDerivAt_const t (1:ℝ)).add he)).sub
        (((hasDerivAt_const t (1:ℝ)).sub he).const_mul 2)
      using 1 <;> first | rfl | (try simp only [id_eq, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply]); ring
  have hd (t : ℝ) : 0 ≤ 1-(1+t)*Real.exp (-t) := by
    have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp t) (Real.exp_pos (-t)).le
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at h
    linarith only [h]
  have he := nonneg_from_derivative_on_Icc (F := F) hu hf (by simp [F]) (fun t _ => hd t)
  apply (div_le_iff₀ (by positivity : 0 < 1+Real.exp (-u))).mpr
  dsimp [F] at he
  linarith only [he]

theorem sine_div_antitone : AntitoneOn (fun x : ℝ => Real.sin x/x) (Ioc 0 Real.pi) := by
  have hs {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ Real.pi) : 0 ≤ Real.sin x - x*Real.cos x := by
    let F := fun t : ℝ => Real.sin t - t*Real.cos t
    have hf (t : ℝ) : HasDerivAt F (t*Real.sin t) t := by
      unfold F
      convert (Real.hasDerivAt_sin t).sub ((hasDerivAt_id t).mul (Real.hasDerivAt_cos t)) using 1 <;> first | rfl | (try simp only [id_eq, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply]); ring
    exact nonneg_from_derivative_on_Icc (F := F) hx hf (by simp [F])
      (fun t ht => mul_nonneg ht.1 (Real.sin_nonneg_of_nonneg_of_le_pi ht.1 (ht.2.trans hx')))
  have hder (x : ℝ) (hx : 0 < x) :
      HasDerivAt (fun x : ℝ => Real.sin x/x) ((Real.cos x*x-Real.sin x)/x^2) x := by
    convert (Real.hasDerivAt_sin x).div (hasDerivAt_id x) hx.ne' using 1
    all_goals first | rfl | (try simp only [id_eq, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply]); ring
  apply antitoneOn_of_deriv_nonpos (convex_Ioc _ _)
    (fun x hx => (hder x hx.1).continuousAt.continuousWithinAt)
    (fun x hx => (hder x (interior_subset hx).1).differentiableAt.differentiableWithinAt)
  intro x hx
  have hx' : x ∈ Ioc 0 Real.pi := interior_subset hx
  rw [(hder x hx'.1).deriv]
  exact div_nonpos_of_nonpos_of_nonneg (by linarith only [hs hx'.1.le hx'.2]) (sq_nonneg _)

end BreakingResonance

#print axioms BreakingResonance.sine_ge_degree_seven
#print axioms BreakingResonance.arctan_ge_degree_three
#print axioms BreakingResonance.exponential_half_ratio_le
#print axioms BreakingResonance.sine_div_antitone
