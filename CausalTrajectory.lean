import GeneralSelection
import Mathlib.Probability.Kernel.IonescuTulcea.Traj

/-! Proper event-history laws from total causal Markov kernels. A coordinate
may encode a structured event, memory, a countable card registry, and a resource
counter. These definitions do not assert that a given program is measurable,
proper, or causally coupled to another program. -/
noncomputable section
open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators
namespace DRGPR.CausalTrajectory

variable {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]

abbrev History (X : ℕ → Type*) (n : ℕ) := (i : Iic n) → X i

structure Controller (X : ℕ → Type*) [∀ n, MeasurableSpace (X n)] where
  next : (n : ℕ) → Kernel (History X n) (X (n+1))
  markov : ∀ n, IsMarkovKernel (next n)

attribute [instance] Controller.markov

def law (C : Controller X) (initial : History X 0) : Measure ((n : ℕ) → X n) :=
  Kernel.traj C.next 0 initial

instance law_probability (C : Controller X) (initial : History X 0) :
    IsProbabilityMeasure (law C initial) := by unfold law; infer_instance

theorem finite_marginal (C : Controller X) (initial : History X 0) (n : ℕ) :
    (law C initial).map (fun x => fun i : Iic n => x i) =
      Kernel.partialTraj C.next 0 n initial := by
  exact Kernel.traj_map_frestrictLe_apply 0 n initial

theorem unique_extension (C : Controller X)
    (K : Kernel (History X 0) ((n : ℕ) → X n))
    (hK : ∀ n, K.map (fun x => fun i : Iic n => x i) = Kernel.partialTraj C.next 0 n) :
    K = Kernel.traj C.next 0 := by
  exact Kernel.eq_traj C.next K hK

theorem conditional_future (C : Controller X) (initial : History X 0)
    (n : ℕ) (f : ((k : ℕ) → X k) → ℝ) (hf : Integrable f (law C initial)) :
    (law C initial)[f|Filtration.piLE n] =ᵐ[law C initial]
      fun x => ∫ y, f y ∂Kernel.traj C.next n (fun i : Iic n => x i) := by
  exact Kernel.condExp_traj (Nat.zero_le n) hf

theorem own_history_law_congr (C D : Controller X) (initial : History X 0)
    (h : C.next = D.next) : law C initial = law D initial := by
  cases C with
  | mk c hc =>
    cases D with
    | mk d hd =>
      change c=d at h
      cases h
      rfl

theorem expected_zero_tail {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : ℕ → Ω → ℝ) (stop : Ω → ℕ) (N : ℕ)
    (hstop : ∀ ω, stop ω ≤ N)
    (hz : ∀ ω r, stop ω ≤ r → f r ω=0) :
    (∫ ω, ∑ r ∈ Finset.range N, f r ω ∂μ) =
      ∫ ω, ∑ r ∈ Finset.range (stop ω), f r ω ∂μ := by
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro ω
  symm
  apply Finset.sum_subset (Finset.range_mono (hstop ω))
  intro r _ hr
  exact hz ω r (Nat.le_of_not_lt (fun h => hr (Finset.mem_range.mpr h)))

/-! Padding preserves a sum but does not imply that a stopped estimator is
unbiased. The latter remains a separate pre-draw conditional-moment contract. -/

theorem prefix_budget_induction (cost : ℕ → ℝ) (B : ℝ)
    (hB : 0 ≤ B)
    (admit : ∀ n, (∑ t ∈ Finset.range n, cost t) ≤ B →
      cost n ≤ B-(∑ t ∈ Finset.range n, cost t)) :
    ∀ n, (∑ t ∈ Finset.range n, cost t) ≤ B := by
  intro n
  induction n with
  | zero => simpa using hB
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have h := admit n ih
    linarith

theorem hard_implies_mean {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (cost : Ω → ℝ) (B : ℝ)
    (hi : Integrable cost μ) (h : ∀ᵐ ω ∂μ, cost ω ≤ B) :
    (∫ ω, cost ω ∂μ) ≤ B := by
  have he := integral_mono_ae hi (integrable_const B) h
  simpa using he

end DRGPR.CausalTrajectory
#print axioms DRGPR.CausalTrajectory.finite_marginal
#print axioms DRGPR.CausalTrajectory.unique_extension
#print axioms DRGPR.CausalTrajectory.conditional_future
#print axioms DRGPR.CausalTrajectory.own_history_law_congr
#print axioms DRGPR.CausalTrajectory.expected_zero_tail
#print axioms DRGPR.CausalTrajectory.prefix_budget_induction
#print axioms DRGPR.CausalTrajectory.hard_implies_mean
