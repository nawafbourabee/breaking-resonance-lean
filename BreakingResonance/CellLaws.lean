import BreakingResonance.TrajectoryEntropy
import BreakingResonance.ForceCorrector

/-! Probability laws of the actual Verlet trajectory and its free flights. -/
noncomputable section
namespace BreakingResonance
open PersistencePays MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def trajectoryLaw (g : E → E) (hg : Measurable g) (μ : ProbabilityMeasure (E×E))
    (h : ℝ) (n : ℕ) : ProbabilityMeasure (E×E) :=
  ⟨(μ : Measure (E×E)).map (fun z=>trajectory g h z n),
    Measure.isProbabilityMeasure_map (trajectory_measurePreserving g hg h n).measurable.aemeasurable⟩

def flightLaw (g : E → E) (hg : Measurable g) (μ : ProbabilityMeasure (E×E))
    (h : ℝ) (n : ℕ) (σ : ℝ) : ProbabilityMeasure (E×E) :=
  ⟨(trajectoryLaw g hg μ h n : Measure (E×E)).map (cellEquiv g hg h σ),
    Measure.isProbabilityMeasure_map (cellEquiv g hg h σ).measurable.aemeasurable⟩

theorem trajectoryLaw_zero (g : E → E) (hg : Measurable g) (μ : ProbabilityMeasure (E×E))
    (h : ℝ) : (trajectoryLaw g hg μ h 0 : Measure (E×E))=(μ : Measure (E×E)) := by
  change (μ : Measure (E×E)).map id=(μ : Measure (E×E))
  exact Measure.map_id

theorem cellState_zero (g : E → E) (h : ℝ) (z : E×E) :
    cellState g h 0 z=kick g (h/2) z := by
  simp [cellState,drift]

theorem flightLaw_initial (g : E → E) (hg : Measurable g) (μ : ProbabilityMeasure (E×E))
    (h : ℝ) : (flightLaw g hg μ h 0 0 : Measure (E×E))=
      (μ : Measure (E×E)).map (kickEquiv g hg (h/2)) := by
  change (trajectoryLaw g hg μ h 0 : Measure (E×E)).map (cellEquiv g hg h 0)=_
  rw [trajectoryLaw_zero]
  congr 1
  funext z
  exact cellState_zero g h z

theorem cellState_endpoint (g : E → E) (h : ℝ) (z : E×E) :
    kick g (h/2) (cellState g h h z)=verlet g h z := rfl

theorem cellState_successor (g : E → E) (h : ℝ) (z : E×E) :
    cellState g h 0 (verlet g h z)=kick g h (cellState g h h z) := by
  rw [cellState_zero,←cellState_endpoint]
  ext <;> simp only [kick,Prod.fst,Prod.snd] <;> module

theorem flightLaw_freeTransport (g : E → E) (hg : Measurable g)
    (μ : ProbabilityMeasure (E×E)) (h : ℝ) (n : ℕ) (σ : ℝ) :
    (flightLaw g hg μ h n σ : Measure (E×E))=
      transportJoint (flightLaw g hg μ h n 0 : Measure (E×E)) σ := by
  change (trajectoryLaw g hg μ h n : Measure (E×E)).map (cellEquiv g hg h σ)=
    ((trajectoryLaw g hg μ h n : Measure (E×E)).map (cellEquiv g hg h 0)).map
      (freeTransport σ)
  rw [Measure.map_map (measurable_freeTransport σ) (cellEquiv g hg h 0).measurable]
  congr 1
  funext z
  change cellState g h σ z=freeTransport σ (cellState g h 0 z)
  rw [cellState_zero]
  rfl

theorem flightLaw_successor (g : E → E) (hg : Measurable g)
    (μ : ProbabilityMeasure (E×E)) (h : ℝ) (n : ℕ) :
    (flightLaw g hg μ h (n+1) 0 : Measure (E×E))=
      (flightLaw g hg μ h n h : Measure (E×E)).map (kickEquiv g hg h) := by
  change ((μ : Measure (E×E)).map (fun z=>trajectory g h z (n+1))).map
      (cellEquiv g hg h 0)=
    (((μ : Measure (E×E)).map (fun z=>trajectory g h z n)).map
      (cellEquiv g hg h h)).map (kickEquiv g hg h)
  rw [Measure.map_map (cellEquiv g hg h 0).measurable
    (trajectory_measurePreserving g hg h (n+1)).measurable,
    Measure.map_map (kickEquiv g hg h).measurable (cellEquiv g hg h h).measurable,
    Measure.map_map ((kickEquiv g hg h).measurable.comp (cellEquiv g hg h h).measurable)
      (trajectory_measurePreserving g hg h n).measurable]
  congr 1
  funext z
  change cellState g h 0 (trajectory g h z (n+1))=
    kick g h (cellState g h h (trajectory g h z n))
  rw [trajectory_succ]
  exact cellState_successor g h (trajectory g h z n)

theorem trajectoryLaw_memLp {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (μ : ProbabilityMeasure (E×E)) (hμ : MemLp id 2 (μ : Measure (E×E)))
    (h : ℝ) (n : ℕ) :
    let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
    MemLp id 2 (trajectoryLaw (gradient U) hg μ h n : Measure (E×E)) := by
  dsimp only [trajectoryLaw]
  exact (memLp_map_measure_iff measurable_id.aestronglyMeasurable
    (trajectory_measurePreserving (gradient U)
      (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable h n).measurable.aemeasurable).mpr
    (trajectory_memLp a hμ h n)

theorem flightLaw_memLp {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (μ : ProbabilityMeasure (E×E)) (hμ : MemLp id 2 (μ : Measure (E×E)))
    (h : ℝ) (n : ℕ) (σ : ℝ) :
    let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
    MemLp id 2 (flightLaw (gradient U) hg μ h n σ : Measure (E×E)) := by
  dsimp only [flightLaw]
  apply (memLp_map_measure_iff measurable_id.aestronglyMeasurable
    (cellEquiv _ _ h σ).measurable.aemeasurable).mpr
  exact drift_memLp (a.kick_memLp (trajectoryLaw_memLp a μ hμ h n) (h/2)) σ

theorem flightLaw_entropy_finite {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (μ : ProbabilityMeasure (E×E)) (hμ : MemLp id 2 (μ : Measure (E×E)))
    (hK : klDiv (μ : Measure (E×E)) (phaseGibbs U)≠∞)
    (h : ℝ) (n : ℕ) (σ : ℝ) :
    let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
    klDiv (flightLaw (gradient U) hg μ h n σ : Measure (E×E)) (phaseGibbs U)≠∞ := by
  dsimp only
  exact (cell_entropy_change a _ (trajectoryLaw_memLp a μ hμ h n)
    (trajectory_entropy_change a (μ : Measure (E×E)) hμ hK h n).1 h σ).1

theorem flightLaw_initial_position (g : E → E) (hg : Measurable g)
    (μ : ProbabilityMeasure (E×E)) (h : ℝ) (n : ℕ) :
    (flightLaw g hg μ h n 0 : Measure (E×E)).fst=
      (trajectoryLaw g hg μ h n : Measure (E×E)).fst := by
  exact map_position_preserving_fst _ (cellEquiv g hg h 0) (fun z=>by
    change (cellState g h 0 z).1=z.1
    rw [cellState_zero]
    rfl)

theorem flightLaw_endpoint_position (g : E → E) (hg : Measurable g)
    (μ : ProbabilityMeasure (E×E)) (h : ℝ) (n : ℕ) :
    (flightLaw g hg μ h n h : Measure (E×E)).fst=
      (flightLaw g hg μ h (n+1) 0 : Measure (E×E)).fst := by
  rw [flightLaw_successor]
  exact (map_position_preserving_fst _ (kickEquiv g hg h) (fun _=>rfl)).symm

theorem trajectoryLaw_entropy_finite {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (μ : ProbabilityMeasure (E×E)) (hμ : MemLp id 2 (μ : Measure (E×E)))
    (hK : klDiv (μ : Measure (E×E)) (phaseGibbs U)≠∞) (h : ℝ) (n : ℕ) :
    let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
    klDiv (trajectoryLaw (gradient U) hg μ h n : Measure (E×E)) (phaseGibbs U)≠∞ :=
  (trajectory_entropy_change a (μ : Measure (E×E)) hμ hK h n).1

end BreakingResonance
