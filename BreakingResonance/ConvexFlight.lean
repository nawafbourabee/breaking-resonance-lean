import BreakingResonance.FlightEntropyContinuity
import BreakingResonance.VerletQuadrature

/-! Convexity controls the quadrature error in each free flight. -/
noncomputable section
namespace BreakingResonance
open PersistencePays MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem potential_convex_combination {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (x y : E) {t : ℝ} (ht : t∈Icc 0 1) :
    U ((1-t) • x+t • y)≤(1-t)*U x+t*U y := by
  let z := (1-t) • x+t • y
  have hx := a.strong_lower_bound z x
  have hy := a.strong_lower_bound z y
  have hx' : U z+⟪gradient U z,x-z⟫≤U x := by
    have := mul_nonneg (show 0 ≤ m / 2 by linarith [a.m_pos]) (sq_nonneg ‖x-z‖)
    linarith
  have hy' : U z+⟪gradient U z,y-z⟫≤U y := by
    have := mul_nonneg (show 0 ≤ m / 2 by linarith [a.m_pos]) (sq_nonneg ‖y-z‖)
    linarith
  have he : (1-t)*⟪gradient U z,x-z⟫+t*⟪gradient U z,y-z⟫=0 := by
    rw [←inner_smul_right,←inner_smul_right,←inner_add_right]
    have hz : (1-t) • (x-z)+t • (y-z)=0 := by dsimp [z]; module
    rw [hz,inner_zero_right]
  have h1 := mul_le_mul_of_nonneg_left hx' (sub_nonneg.mpr ht.2)
  have h2 := mul_le_mul_of_nonneg_left hy' ht.1
  change U z≤_
  nlinarith

theorem potential_flight_chord {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (x v : E) {h σ : ℝ} (hh : 0<h) (hσ : σ∈Icc 0 h) :
    U (x+σ • v)≤(1-σ/h)*U x+(σ/h)*U (x+h • v) := by
  have ht : σ/h∈Icc 0 1 :=
    ⟨div_nonneg hσ.1 hh.le,(div_le_one hh).mpr hσ.2⟩
  have he : (1-σ/h) • x+(σ/h) • (x+h • v)=x+σ • v := by
    rw [smul_add,smul_smul,div_mul_cancel₀ σ hh.ne']
    module
  simpa only [he] using potential_convex_combination a x (x+h • v) ht

theorem flight_mean_chord {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (μ : Measure (E×E)) [IsProbabilityMeasure μ] (hμ : MemLp id 2 μ)
    {h σ : ℝ} (hh : 0<h) (hσ : σ∈Icc 0 h) :
    (∫z,U (z.1+σ • z.2) ∂μ)≤
      (1-σ/h)*(∫z,U z.1 ∂μ)+(σ/h)*(∫z,U (z.1+h • z.2) ∂μ) := by
  have hi := a.potential_integrable (hμ.fst.add (hμ.snd.const_smul σ))
  have h0 := a.potential_integrable hμ.fst
  have h1 := a.potential_integrable (hμ.fst.add (hμ.snd.const_smul h))
  change Integrable (fun z : E×E=>U (z.1+σ • z.2)) μ at hi
  change Integrable (fun z : E×E=>U z.1) μ at h0
  change Integrable (fun z : E×E=>U (z.1+h • z.2)) μ at h1
  have hb := integral_mono hi
    ((h0.const_mul (1-σ/h)).add (h1.const_mul (σ/h)))
    (fun z=>potential_flight_chord a z.1 z.2 hh hσ)
  change (∫z,U (z.1+σ • z.2) ∂μ)≤
    (∫z,(1-σ/h)*U z.1+(σ/h)*U (z.1+h • z.2) ∂μ) at hb
  rw [integral_add (μ:=μ) (f:=fun z : E×E=>(1-σ/h)*U z.1)
    (g:=fun z : E×E=>(σ/h)*U (z.1+h • z.2)) (h0.const_mul (1-σ/h)) (h1.const_mul (σ/h)),
    integral_const_mul,integral_const_mul] at hb
  exact hb

theorem weighted_chord_integral (A x y : ℝ) {h : ℝ} (hh : h≠0) :
    (∫σ in (0:ℝ)..h,(A-σ)*((1-σ/h)*x+(σ/h)*y))=
      (h*A/2-h^2/6)*x+(h*A/2-h^2/3)*y := by
  have he (σ : ℝ) : (A-σ)*((1-σ/h)*x+(σ/h)*y)=
      A*x+((A/h)*(y-x)-x)*σ+((x-y)/h)*σ^2 := by ring
  simp_rw [he]
  rw [intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_add intervalIntegrable_const
      (by apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_const,intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,integral_id,integral_pow]
  simp only [sub_zero,smul_eq_mul,zero_pow (by norm_num : (2:ℕ)≠0),
    zero_pow (by norm_num : (3:ℕ)≠0)]
  norm_num
  field_simp
  <;> ring

theorem flight_weighted_potential_chord {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (μ : Measure (E×E)) [IsProbabilityMeasure μ] (hμ : MemLp id 2 μ)
    {A h : ℝ} (hh : 0<h) (hA : h≤A) (u : ℝ) :
    (∫σ in (0:ℝ)..h,(A-σ)*((∫z,U (z.1+σ • z.2) ∂μ)-u))≤
      (h*A/2-h^2/6)*((∫z,U z.1 ∂μ)-u)+
      (h*A/2-h^2/3)*((∫z,U (z.1+h • z.2) ∂μ)-u) := by
  have hc := continuous_freeFlight_potential a μ hμ
  have hb := intervalIntegral.integral_mono_on (μ:=volume) hh.le
    (show IntervalIntegrable (fun σ=>(A-σ)*((∫z,U (z.1+σ • z.2) ∂μ)-u)) volume 0 h from
      (by apply Continuous.intervalIntegrable; fun_prop))
    (show IntervalIntegrable (fun σ=>(A-σ)*((1-σ/h)*((∫z,U z.1 ∂μ)-u)+
      (σ/h)*((∫z,U (z.1+h • z.2) ∂μ)-u))) volume 0 h from
      (by apply Continuous.intervalIntegrable; fun_prop)) ?_
  · rw [weighted_chord_integral _ _ _ hh.ne'] at hb
    exact hb
  · intro σ hσ
    have hm := mul_le_mul_of_nonneg_left (flight_mean_chord a μ hμ hh hσ)
      (sub_nonneg.mpr (hσ.2.trans hA))
    nlinarith

end BreakingResonance
