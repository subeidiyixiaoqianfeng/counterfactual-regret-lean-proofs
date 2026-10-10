import RandomStochastic
import DeepChecks

/-! Finite algorithm-to-endpoint composition, without assuming selection regret.
Deployment and representation comparisons remain the manuscript's explicit
interface hypotheses. This is not a construction of an arbitrary real agent. -/
noncomputable section
open scoped BigOperators
namespace DRGPR.InterfaceCompletion

structure Experiment (Ω I H O : Type*) [Fintype Ω] [Fintype I] [Fintype H] [Fintype O]
    [DecidableEq I] [DecidableEq H] [DecidableEq O] where
  m : Ω → ℝ
  m_nonneg : ∀ ω, 0 ≤ m ω
  m_sum : ∑ ω, m ω = 1
  X : ∀ r : ℕ, RandomStochastic.Realization Ω I H O m
  ν : Ω → I → ℝ
  P : Ω → ℕ → I → I → ℝ
  z : Ω → ℕ → I → ℝ
  η : ℝ
  b : ℝ
  C : ℝ
  V : ℝ
  R : ℕ
  v : ℕ → H → I
  bridge_active : ∀ r h, 0 < ((X r).model h).p (v r h)
  rate_pos : 0 < η
  cap_nonneg : 0 ≤ b
  prior_nonneg : ∀ ω i, 0 ≤ ν ω i
  prior_sum : ∀ ω, ∑ i, ν ω i = 1
  transition_nonneg : ∀ ω r i j, 0 ≤ P ω r i j
  transition_sum : ∀ ω r i, ∑ j, P ω r i j = 1
  algorithm_law : ∀ ω r i, Growing.prob (ν ω) (P ω) (z ω) η r i = (X r).prob ω i
  observation_law : ∀ ω r i, z ω r i = (X r).est ω i
  initial_bridge : ∀ ω, 0 < ν ω (v 0 ((X 0).sample ω).1)
  bridge_transition : ∀ ω r, 0 < P ω r (v r ((X r).sample ω).1)
    (v (r+1) ((X (r+1)).sample ω).1)
  code : ∀ ω, -(Real.log (ν ω (v 0 ((X 0).sample ω).1)) +
    ∑ r ∈ Finset.range R, Real.log (P ω r (v r ((X r).sample ω).1)
      (v (r+1) ((X (r+1)).sample ω).1))) ≤ C
  capped : ∀ r h, ((X r).model h).d ≤ b
  capacity : (∑ r ∈ Finset.range (R+1), (X r).activity) ≤ V

namespace Experiment
variable {Ω I H O : Type*} [Fintype Ω] [Fintype I] [Fintype H] [Fintype O]
  [DecidableEq I] [DecidableEq H] [DecidableEq O]

def selected (E : Experiment Ω I H O) : ℝ :=
  ∑ r ∈ Finset.range (E.R+1), mean E.m (E.X r).selectedLoss
def available (E : Experiment Ω I H O) : ℝ :=
  ∑ r ∈ Finset.range (E.R+1), mean E.m ((E.X r).bridgeLoss (E.v r))
def selectionBudget (E : Experiment Ω I H O) : ℝ := E.C/E.η+E.η*E.b*E.V/2

theorem selection (E : Experiment Ω I H O) : E.selected-E.available ≤ E.selectionBudget := by
  have hs := RandomStochastic.expected_growing_selection E.m E.m_nonneg E.m_sum
    E.X E.ν E.P E.z E.η E.b E.C E.V E.R E.v E.bridge_active E.rate_pos E.cap_nonneg
    E.prior_nonneg E.prior_sum E.transition_nonneg E.transition_sum
    E.algorithm_law E.observation_law E.initial_bridge E.bridge_transition E.code E.capped E.capacity
  simp_rw [mean_sub] at hs
  simpa only [selected, available, selectionBudget, Finset.sum_sub_distrib] using hs

theorem transfer (E : Experiment Ω I H O)
    (realA refA aligned clean refPath refM realM : Ω → ℝ)
    (cpA acquisition generation alignment response representation cpC : ℝ)
    (h₁ : mean E.m (fun ω => realA ω-refA ω) ≤ cpA)
    (h₂ : mean E.m refA-E.selected ≤ acquisition)
    (h₄ : E.available-mean E.m aligned ≤ generation)
    (h₅ : mean E.m (fun ω => aligned ω-clean ω) ≤ alignment)
    (h₆ : mean E.m (fun ω => clean ω-refPath ω) ≤ response)
    (h₇ : mean E.m (fun ω => refPath ω-refM ω) ≤ representation)
    (h₈ : mean E.m (fun ω => refM ω-realM ω) ≤ cpC) :
    mean E.m realA-mean E.m realM ≤
      cpA+acquisition+E.selectionBudget+generation+alignment+response+representation+cpC := by
  simp_rw [mean_sub] at h₁ h₅ h₆ h₇ h₈
  have hs := E.selection
  linarith

end Experiment

theorem uniform_counterfactual_transfer {M : Type*} [Nonempty M]
    (learner : ℝ) (comparator bound : M → ℝ) (U : ℝ)
    (htransfer : ∀ μ, learner-comparator μ ≤ bound μ)
    (huniform : ∀ μ, bound μ ≤ U) :
    learner-sInf (Set.range comparator) ≤ U := by
  apply DRGPR.infimum_transfer learner U (Set.range comparator)
  · exact Set.range_nonempty comparator
  · intro c hc
    obtain ⟨μ, rfl⟩ := hc
    exact le_trans (htransfer μ) (huniform μ)

theorem zero_tail_sum (f : ℕ → ℝ) (k n : ℕ) (hkn : k ≤ n)
    (hz : ∀ r, k ≤ r → f r = 0) :
    (∑ r ∈ Finset.range n, f r) = ∑ r ∈ Finset.range k, f r := by
  symm
  apply Finset.sum_subset (Finset.range_mono hkn)
  intro r _ hr
  exact hz r (Nat.le_of_not_lt (fun h => hr (Finset.mem_range.mpr h)))

def share {I : Type*} [DecidableEq I] (α : ℝ) (ν : I → ℝ) (i j : I) : ℝ :=
  (1-α)*(if i=j then 1 else 0)+α*ν j

theorem share_row_sum {I : Type*} [Fintype I] [DecidableEq I]
    (α : ℝ) (ν : I → ℝ) (hν : ∑ j, ν j=1) (i : I) :
    (∑ j, share α ν i j)=1 := by
  simp [share, Finset.sum_add_distrib, ← Finset.mul_sum, hν]

theorem share_marginal {I : Type*} [Fintype I] [DecidableEq I]
    (α : ℝ) (ν w : I → ℝ) (hw : ∑ i, w i=1) (j : I) :
    (∑ i, w i*share α ν i j)=(1-α)*w j+α*ν j := by
  simp only [share, mul_add, Finset.sum_add_distrib]
  have ha : (∑ i, w i*((1-α)*(if i=j then 1 else 0)))=(1-α)*w j := by
    simp [mul_ite]
    ring
  rw [ha, ← Finset.sum_mul, hw]
  ring

theorem newborn_share_positive {I : Type*} [Fintype I] [DecidableEq I]
    (α : ℝ) (ν w : I → ℝ) (hw : ∑ i, w i=1) (j : I)
    (hα : 0 < α) (hν : 0 < ν j) (hnew : w j=0) :
    0 < ∑ i, w i*share α ν i j := by
  rw [share_marginal α ν w hw j, hnew]
  simpa using mul_pos hα hν

theorem exact_resource_step (spent reserved cost budget : ℝ)
    (hreserve : spent+reserved ≤ budget) (hcost : cost ≤ reserved) :
    spent+cost ≤ budget := by linarith

theorem resource_induction (spent budget : ℕ → ℝ)
    (hstart : spent 0 ≤ budget 0)
    (step : ∀ n, spent n ≤ budget n → spent (n+1) ≤ budget (n+1)) :
    ∀ n, spent n ≤ budget n := by
  intro n
  induction n with
  | zero => exact hstart
  | succ n ih => exact step n ih

theorem approximate_probability_bias (p q qt l : ℝ)
    (hp : 0 < p) (hqt : 0 < qt) :
    p*(q*l/(p*qt))-l=(q/qt-1)*l := by
  field_simp [hp.ne', hqt.ne']
  ring

theorem geometric_stability (error innovation : ℕ → ℝ) (β : ℝ)
    (hβ : 0 ≤ β) (initial : error 0=0)
    (step : ∀ n, error (n+1) ≤ β*error n+innovation n) (n : ℕ) :
    error n ≤ ∑ j ∈ Finset.range n, β^(n-1-j)*innovation j := by
  induction n with
  | zero => simp [initial]
  | succ n ih =>
    have hi := add_le_add_right (mul_le_mul_of_nonneg_left ih hβ) (innovation n)
    have he : β*(∑ j ∈ Finset.range n, β^(n-1-j)*innovation j) =
        ∑ j ∈ Finset.range n, β^(n-j)*innovation j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      have h : n-j=(n-1-j)+1 := by have := Finset.mem_range.mp hj; omega
      rw [h, pow_succ]
      ring
    rw [he] at hi
    simpa [Finset.sum_range_succ] using le_trans (step n) hi

end DRGPR.InterfaceCompletion

#print axioms DRGPR.InterfaceCompletion.Experiment.selection
#print axioms DRGPR.InterfaceCompletion.Experiment.transfer
#print axioms DRGPR.InterfaceCompletion.uniform_counterfactual_transfer
#print axioms DRGPR.InterfaceCompletion.zero_tail_sum
#print axioms DRGPR.InterfaceCompletion.share_row_sum
#print axioms DRGPR.InterfaceCompletion.share_marginal
#print axioms DRGPR.InterfaceCompletion.newborn_share_positive
#print axioms DRGPR.InterfaceCompletion.exact_resource_step
#print axioms DRGPR.InterfaceCompletion.resource_induction
#print axioms DRGPR.InterfaceCompletion.approximate_probability_bias
#print axioms DRGPR.InterfaceCompletion.geometric_stability
