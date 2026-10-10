import DependentSelection
import InterfaceCompletion

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace DRGPR.DependentTransfer

structure Experiment (Ω : Type*) (I : Ω → ℕ → Type*) [MeasurableSpace Ω] [∀ ω r, Fintype (I ω r)]
    (μ : Measure Ω) where
  ν : ∀ ω, I ω 0 → ℝ
  P : ∀ ω r, I ω r → I ω (r+1) → ℝ
  z : ∀ ω r, I ω r → ℝ
  v : ∀ ω r, I ω r
  selected : ℕ → Ω → ℝ
  available : ℕ → Ω → ℝ
  η : ℝ
  C : ℝ
  V : ℝ
  R : ℕ
  rate_pos : 0 < η
  prior_nonneg : ∀ ω i, 0 ≤ ν ω i
  prior_sum : ∀ ω, ∑ i, ν ω i=1
  transition_nonneg : ∀ ω r i j, 0 ≤ P ω r i j
  transition_sum : ∀ ω r i, ∑ j, P ω r i j=1
  estimate_nonneg : ∀ ω r i, 0 ≤ z ω r i
  initial_path : ∀ ω, 0 < ν ω (v ω 0)
  transition_path : ∀ ω r, 0 < P ω r (v ω r) (v ω (r+1))
  code : ∀ ω, -(Real.log (ν ω (v ω 0))+
    ∑ r ∈ Finset.range R, Real.log (P ω r (v ω r) (v ω (r+1)))) ≤ C
  linear_integrable : ∀ r, Integrable (DependentSelection.linear ν P z η v r) μ
  selected_integrable : ∀ r, Integrable (selected r) μ
  available_integrable : ∀ r, Integrable (available r) μ
  square_integrable : ∀ r, Integrable (DependentSelection.square ν P z η r) μ
  moment : ∀ r, (∫ ω, DependentSelection.linear ν P z η v r ω ∂μ) =
    ∫ ω, selected r ω-available r ω ∂μ
  capacity : (∑ r ∈ Finset.range (R+1), ∫ ω, DependentSelection.square ν P z η r ω ∂μ) ≤ V

namespace Experiment
variable {Ω : Type*} {I : Ω → ℕ → Type*} [MeasurableSpace Ω] [∀ ω r, Fintype (I ω r)]
  {μ : Measure Ω} [IsProbabilityMeasure μ]

def selectedTotal (E : Experiment Ω I μ) : ℝ :=
  ∑ r ∈ Finset.range (E.R+1), ∫ ω, E.selected r ω ∂μ
def availableTotal (E : Experiment Ω I μ) : ℝ :=
  ∑ r ∈ Finset.range (E.R+1), ∫ ω, E.available r ω ∂μ
def selectionBudget (E : Experiment Ω I μ) : ℝ := E.C/E.η+E.η*E.V/2

theorem selection (E : Experiment Ω I μ) : E.selectedTotal-E.availableTotal ≤ E.selectionBudget := by
  have h := DependentSelection.expected_growing_selection μ E.ν E.P E.z E.η E.C E.V E.R E.v
    (fun r ω => E.selected r ω-E.available r ω)
    E.rate_pos E.prior_nonneg E.prior_sum E.transition_nonneg E.transition_sum
    E.estimate_nonneg E.initial_path E.transition_path E.code E.linear_integrable
    (fun r => (E.selected_integrable r).sub (E.available_integrable r))
    E.square_integrable E.moment E.capacity
  simp_rw [integral_sub (E.selected_integrable _) (E.available_integrable _)] at h
  simpa only [selectedTotal, availableTotal, selectionBudget, Finset.sum_sub_distrib] using h

theorem transfer (E : Experiment Ω I μ)
    (realA refA aligned clean refPath refM realM : Ω → ℝ)
    (cpA acquisition generation alignment response representation cpC : ℝ)
    (h₁ : (∫ ω, realA ω ∂μ)-(∫ ω, refA ω ∂μ) ≤ cpA)
    (h₂ : (∫ ω, refA ω ∂μ)-E.selectedTotal ≤ acquisition)
    (h₄ : E.availableTotal-(∫ ω, aligned ω ∂μ) ≤ generation)
    (h₅ : (∫ ω, aligned ω ∂μ)-(∫ ω, clean ω ∂μ) ≤ alignment)
    (h₆ : (∫ ω, clean ω ∂μ)-(∫ ω, refPath ω ∂μ) ≤ response)
    (h₇ : (∫ ω, refPath ω ∂μ)-(∫ ω, refM ω ∂μ) ≤ representation)
    (h₈ : (∫ ω, refM ω ∂μ)-(∫ ω, realM ω ∂μ) ≤ cpC) :
    (∫ ω, realA ω ∂μ)-(∫ ω, realM ω ∂μ) ≤
      cpA+acquisition+E.selectionBudget+generation+alignment+response+representation+cpC := by
  have h := E.selection
  linarith

end Experiment

theorem counterfactual_infimum {M : Type*} [Nonempty M]
    (learner : ℝ) (loss bound : M → ℝ) (U : ℝ)
    (h : ∀ c, learner-loss c ≤ bound c) (hu : ∀ c, bound c ≤ U) :
    learner-sInf (Set.range loss) ≤ U :=
  InterfaceCompletion.uniform_counterfactual_transfer learner loss bound U h hu

end DRGPR.DependentTransfer
#print axioms DRGPR.DependentTransfer.Experiment.selection
#print axioms DRGPR.DependentTransfer.Experiment.transfer
#print axioms DRGPR.DependentTransfer.counterfactual_infimum


