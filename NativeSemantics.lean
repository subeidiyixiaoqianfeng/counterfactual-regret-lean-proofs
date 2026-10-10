import CausalTrajectory
import DeploymentCoupling
import ModelMain

/-! Typed native executions. A native controller is an arbitrary causal
kernel, not an externally installed Bandit. The conditional selection
experiment remains a separate reference object. -/
noncomputable section
open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators
namespace DRGPR.NativeSemantics

variable {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]

/-- A coordinate is a structured task event. Scores use only the completed
finite prefix. Proper internal computation is represented by the supplied
normalized task-event kernels, not inferred for arbitrary generated code. -/
structure Execution (X : ℕ → Type*) [∀ n, MeasurableSpace (X n)] (T : ℕ) where
  controller : CausalTrajectory.Controller X
  initial : CausalTrajectory.History X 0
  score : (t : Fin T) → CausalTrajectory.History X (t.val + 1) → ℝ
  score_measurable : ∀ t, Measurable (score t)
  score_nonneg : ∀ t h, 0 ≤ score t h
  score_le_one : ∀ t h, score t h ≤ 1

namespace Execution
variable {T : ℕ} (A : Execution X T)

def law : Measure ((n : ℕ) → X n) := CausalTrajectory.law A.controller A.initial
instance probability : IsProbabilityMeasure A.law := by unfold law; infer_instance

def stage (t : Fin T) (h : (n : ℕ) → X n) : ℝ :=
  A.score t (fun i : Iic (t.val + 1) => h i)
def loss (h : (n : ℕ) → X n) : ℝ := ∑ t, A.stage t h
def expectedLoss : ℝ := ∫ h, A.loss h ∂A.law

theorem stage_measurable (t : Fin T) : Measurable (A.stage t) := by
  exact (A.score_measurable t).comp
    (measurable_pi_lambda _ (fun i => measurable_pi_apply (i : ℕ)))

theorem loss_measurable : Measurable A.loss := by
  exact Finset.measurable_sum _ (fun t _ => A.stage_measurable t)

theorem loss_bounds (h : (n : ℕ) → X n) : 0 ≤ A.loss h ∧ A.loss h ≤ T := by
  constructor
  · exact sum_nonneg (fun t _ => A.score_nonneg t _)
  · calc
      A.loss h ≤ ∑ _t : Fin T, (1 : ℝ) :=
        sum_le_sum (fun t _ => A.score_le_one t _)
      _ = T := by simp

theorem loss_integrable : Integrable A.loss A.law := by
  apply Integrable.mono' (integrable_const (T : ℝ)) A.loss_measurable.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro h
  rw [Real.norm_eq_abs, abs_of_nonneg (A.loss_bounds h).1]
  exact (A.loss_bounds h).2

theorem expected_bounds : 0 ≤ A.expectedLoss ∧ A.expectedLoss ≤ T := by
  constructor
  · exact integral_nonneg (fun h => (A.loss_bounds h).1)
  · have h := integral_mono_ae A.loss_integrable (integrable_const (T : ℝ))
      (Filter.Eventually.of_forall (fun h => (A.loss_bounds h).2))
    simpa [expectedLoss] using h
end Execution

variable {Ω : Type*} [MeasurableSpace Ω] {T : ℕ}

/-- Realization of a specified own-history execution under a joint coupling.
The marginal is the actual causal law, not an arbitrary named loss function. -/
structure Realization (A : Execution X T) (μ : Measure Ω) where
  path : Ω → ((n : ℕ) → X n)
  measurable_path : Measurable path
  marginal : μ.map path = A.law

namespace Realization
variable {A : Execution X T} {μ : Measure Ω} (W : Realization A μ)
def total (ω : Ω) : ℝ := A.loss (W.path ω)

theorem total_integrable [IsProbabilityMeasure μ] : Integrable W.total μ := by
  apply Integrable.mono' (integrable_const (T : ℝ))
    (A.loss_measurable.comp W.measurable_path).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro ω
  change ‖A.loss (W.path ω)‖ ≤ (T : ℝ)
  rw [Real.norm_eq_abs, abs_of_nonneg (A.loss_bounds (W.path ω)).1]
  exact (A.loss_bounds (W.path ω)).2

theorem expected_total :
    (∫ ω, W.total ω ∂μ) = A.expectedLoss := by
  exact (DeploymentCoupling.marginal_expectation μ A.law W.path A.loss
    W.measurable_path W.marginal A.loss_integrable).symm
end Realization

variable {I : Ω → ℕ → Type*} [∀ ω r, Fintype (I ω r)]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- An interface witness couples the native learner and comparator to the
reference selection proof. It does not identify their decision kernels. -/
structure Witness (A C : Execution X T)
    (E : DependentTransfer.Experiment Ω I μ) (B : ModelMain.Budget) where
  learner : Realization A μ
  comparator : Realization C μ
  interfaces : ModelMain.Certificates E B
  realA_eq : interfaces.realA = learner.total
  realM_eq : interfaces.realM = comparator.total
  horizon_eq : B.T = T

theorem native_transfer (A C : Execution X T)
    (E : DependentTransfer.Experiment Ω I μ) (B : ModelMain.Budget)
    (W : Witness A C E B) :
    A.expectedLoss - C.expectedLoss ≤ B.bound E.η E.C := by
  have h := ModelMain.main_fixed E B W.interfaces
  rw [W.realA_eq, W.realM_eq, W.learner.expected_total,
    W.comparator.expected_total] at h
  exact h

/-- The learner marginal is fixed by its specified execution for every
comparator. Thus choosing a comparator never changes the learner law. -/
theorem native_counterfactual {M : Type*} [Nonempty M]
    (A : Execution X T) (C : M → Execution X T)
    (E : M → DependentTransfer.Experiment Ω I μ)
    (B : ModelMain.Budget) (η code : ℝ)
    (W : ∀ m, Witness A (C m) (E m) B)
    (hη : ∀ m, (E m).η = η) (hc : ∀ m, (E m).C = code) :
    A.expectedLoss - sInf (Set.range (fun m => (C m).expectedLoss)) ≤
      B.bound η code := by
  apply DRGPR.infimum_transfer A.expectedLoss (B.bound η code) _
  · exact Set.range_nonempty _
  · intro x hx
    obtain ⟨m, rfl⟩ := hx
    simpa [hη m, hc m] using native_transfer A (C m) (E m) B (W m)

end DRGPR.NativeSemantics
#print axioms DRGPR.NativeSemantics.Execution.stage_measurable
#print axioms DRGPR.NativeSemantics.Execution.loss_measurable
#print axioms DRGPR.NativeSemantics.Execution.loss_bounds
#print axioms DRGPR.NativeSemantics.Execution.loss_integrable
#print axioms DRGPR.NativeSemantics.Execution.expected_bounds
#print axioms DRGPR.NativeSemantics.Realization.total_integrable
#print axioms DRGPR.NativeSemantics.Realization.expected_total
#print axioms DRGPR.NativeSemantics.native_transfer
#print axioms DRGPR.NativeSemantics.native_counterfactual
