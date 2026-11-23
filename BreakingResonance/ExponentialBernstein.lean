import BreakingResonance.FourierTrig
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-! An exact rational Bernstein certificate for the exponential comparison
in Appendix C. Its coefficients are scaled by a common positive integer. -/
noncomputable section
namespace BreakingResonance

def exponentialSinePolynomial (y : ℝ) : ℝ :=
  1 - y/6 + y^2/120 - y^3/5040

def exponentialReferencePolynomial (y : ℝ) : ℝ :=
  (1-y/768)^2 * exponentialSinePolynomial y ^ 2

/-- The polynomial D(P(y) - 1/250), where P is the expression in Appendix C. -/
def exponentialComparisonPolynomial (y : ℝ) : ℝ :=
    (93584273965056 : ℝ) * y^0 +
    (-57937493376000 : ℝ) * y^1 +
    (12042372384000 : ℝ) * y^2 +
    (-1017014342400 : ℝ) * y^3 +
    (48417062400 : ℝ) * y^4 +
    (-1300666800 : ℝ) * y^5 +
    (17895300 : ℝ) * y^6 +
    (-40400 : ℝ) * y^7 +
    (25 : ℝ) * y^8

/-- The coefficients already include the binomial factors of degree eight. -/
def exponentialBernsteinCertificate : Fin 7 → Fin 9 → ℕ :=
  ![![93584273965056,690736698344448,2226839589773568,4095269201108736,4698685840504320,3443776745721936,1574424370730868,410470702679848,46719272881181],
    ![46719272881181,337037663419048,1060393095905268,1900010928710336,2120169503702320,1508390513348736,668018675096768,168338295912448,18476853805056],
    ![18476853805056,127291364968448,380690158488768,645047235831936,676738282198320,449788890131136,184823733319668,42913972433448,4312435553181],
    ![4312435553181,26084996417448,67020901207668,95293353120336,82288918264320,45160696225536,16405338509568,4047412507648,558864736256],
    ![558864736256,4894423272448,22334413863168,62092117089536,107655269048320,116378908591536,76244767314068,27729737721448,4301871713181],
    ![4301871713181,41100209689448,169838071090068,396498858080736,572321978734320,523457447895936,296509997746368,95183208718848,13267805101056],
    ![13267805101056,117101672898048,449939247000768,983249677950336,1336990636462320,1158688553912736,625166521709268,192047750265448,25723444753181]]

theorem exponentialComparisonPolynomial_identity (y : ℝ) :
    y * exponentialComparisonPolynomial y =
      (599298932736000 : ℝ) * (y - (5/8 : ℝ)*(4+y)*(1-exponentialReferencePolynomial y) - y/250) := by
  unfold exponentialComparisonPolynomial exponentialReferencePolynomial exponentialSinePolynomial
  ring

set_option maxHeartbeats 2500000 in
theorem exponentialComparisonPolynomial_bernstein (j : Fin 7) (t : ℝ) :
    exponentialComparisonPolynomial ((j.val : ℝ)+t) =
      ∑ i : Fin 9, (exponentialBernsteinCertificate j i : ℝ) * t^i.val * (1-t)^(8-i.val) := by
  fin_cases j <;>
    norm_num [exponentialComparisonPolynomial, exponentialBernsteinCertificate, Fin.sum_univ_succ] <;>
    ring

theorem exponentialComparisonPolynomial_nonneg {y : ℝ} (hy : 0 ≤ y) (hy' : y ≤ 7) :
    0 ≤ exponentialComparisonPolynomial y := by
  have hj : ∃ j : Fin 7, (j.val : ℝ) ≤ y ∧ y ≤ (j.val : ℝ)+1 := by
    let j := Nat.floor y
    by_cases hj : j < 7
    · exact ⟨⟨j,hj⟩, Nat.floor_le hy, (Nat.lt_floor_add_one y).le⟩
    · have h7 : (7 : ℝ) ≤ y := (Nat.le_floor_iff hy).mp (le_of_not_gt hj)
      exact ⟨6, by norm_num; linarith only [h7], by norm_num; exact hy'⟩
  obtain ⟨j,hj₀,hj₁⟩ := hj
  let t := y-(j.val : ℝ)
  have ht : 0 ≤ t := sub_nonneg.mpr hj₀
  have ht' : t ≤ 1 := by dsimp [t]; linarith only [hj₁]
  have he : (j.val : ℝ)+t = y := by dsimp [t]; ring
  rw [← he, exponentialComparisonPolynomial_bernstein]
  exact Finset.sum_nonneg fun i _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg ht _))
      (pow_nonneg (sub_nonneg.mpr ht') _)

theorem exponentialReferencePolynomial_comparison {y : ℝ} (hy : 0 ≤ y) (hy' : y ≤ 7) :
    (5/8 : ℝ)*(4+y)*(1-exponentialReferencePolynomial y) ≤ y := by
  have h := mul_nonneg hy (exponentialComparisonPolynomial_nonneg hy hy')
  rw [exponentialComparisonPolynomial_identity] at h
  have hh := nonneg_of_mul_nonneg_right h (by norm_num : (0 : ℝ) < 599298932736000)
  linarith only [hh, hy]

end BreakingResonance

#print axioms BreakingResonance.exponentialReferencePolynomial_comparison
