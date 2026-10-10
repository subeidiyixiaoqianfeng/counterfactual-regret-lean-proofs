import DependentTransfer
import FiniteObservation

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace DRGPR.ObservationBridgeV19

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  {H : Type} [Fintype H]
  {I O : H → Type} [∀ h, Fintype (I h)] [∀ h, Fintype (O h)]
  [∀ h, DecidableEq (I h)]

/-- The finite predraw-history law is connected to the same actual sample
space by disintegration against every finite test, not by a regret moment.
Round probabilities must separately be identified with the weight recurrence.
This is a law interface, not an estimator-bias assumption. -/
structure LawWitness where
  weight : H → ℝ
  weight_nonneg : ∀ h, 0 ≤ weight h
  weight_sum : ∑ h, weight h = 1
  round : ∀ h, FiniteObservation.Round (I h) (O h)
  history : Ω → H
  draw : ∀ ω, I (history ω)
  outcome : ∀ ω, O (history ω)
  comparator : ∀ h, I h
  test_integrable : ∀ f : (h : H) → I h → O h → ℝ,
    Integrable (fun ω => f (history ω) (draw ω) (outcome ω)) μ
  disintegration : ∀ f : (h : H) → I h → O h → ℝ,
    (∫ ω, f (history ω) (draw ω) (outcome ω) ∂μ) =
      ∑ h, weight h * (round h).avg (f h)

variable {μ}
def LawWitness.linear (W : LawWitness μ (I:=I) (O:=O)) (ω : Ω) : ℝ :=
  let D := W.round (W.history ω)
  (∑ i, D.p i * D.estimate (W.draw ω) (W.outcome ω) i) -
    D.estimate (W.draw ω) (W.outcome ω) (W.comparator (W.history ω))
def LawWitness.selected (W : LawWitness μ (I:=I) (O:=O)) (ω : Ω) : ℝ :=
  (W.round (W.history ω)).loss (W.draw ω)
def LawWitness.available (W : LawWitness μ (I:=I) (O:=O)) (ω : Ω) : ℝ :=
  (W.round (W.history ω)).loss (W.comparator (W.history ω))
def LawWitness.square (W : LawWitness μ (I:=I) (O:=O)) (ω : Ω) : ℝ :=
  let D := W.round (W.history ω)
  ∑ i, D.p i * (D.estimate (W.draw ω) (W.outcome ω) i)^2

theorem LawWitness.moment (W : LawWitness μ (I:=I) (O:=O)) :
    (∫ ω, W.linear ω ∂μ) = ∫ ω, W.selected ω-W.available ω ∂μ := by
  change (∫ ω, (fun h i o =>
    (∑ j, (W.round h).p j*(W.round h).estimate i o j)-
      (W.round h).estimate i o (W.comparator h)) (W.history ω) (W.draw ω) (W.outcome ω) ∂μ) = _
  rw [W.disintegration (fun h i o =>
    (∑ j, (W.round h).p j*(W.round h).estimate i o j)-
      (W.round h).estimate i o (W.comparator h))]
  change _ = ∫ ω, (fun h i _ => (W.round h).loss i-(W.round h).loss (W.comparator h))
    (W.history ω) (W.draw ω) (W.outcome ω) ∂μ
  rw [W.disintegration (fun h i _ => (W.round h).loss i-(W.round h).loss (W.comparator h))]
  apply Finset.sum_congr rfl
  intro h _
  rw [(W.round h).regret_linear (W.comparator h)]

theorem LawWitness.second (W : LawWitness μ (I:=I) (O:=O)) :
    (∫ ω, W.square ω ∂μ) ≤
      ∑ h, W.weight h * ((W.round h).d^2 * ∑ i, 1/(W.round h).q i) := by
  change (∫ ω, (fun h i o => ∑ j, (W.round h).p j*((W.round h).estimate i o j)^2)
    (W.history ω) (W.draw ω) (W.outcome ω) ∂μ) ≤ _
  rw [W.disintegration (fun h i o => ∑ j, (W.round h).p j*((W.round h).estimate i o j)^2)]
  exact Finset.sum_le_sum (fun h _ => mul_le_mul_of_nonneg_left
    (W.round h).weighted_second (W.weight_nonneg h))

/-- Pullbacks identify the derived score with the actual weight-recursion
score pointwise. Equality of isolated identity marginals is not enough. -/
theorem identified_moment (W : LawWitness μ (I:=I) (O:=O))
    (linear selected available : Ω → ℝ)
    (hl : linear = W.linear) (hs : selected = W.selected) (ha : available = W.available) :
    (∫ ω, linear ω ∂μ) = ∫ ω, selected ω-available ω ∂μ := by
  rw [hl, hs, ha]
  exact W.moment

end DRGPR.ObservationBridgeV19
#print axioms DRGPR.ObservationBridgeV19.LawWitness.moment
#print axioms DRGPR.ObservationBridgeV19.LawWitness.second
#print axioms DRGPR.ObservationBridgeV19.identified_moment
