import GranularController

noncomputable section
open scoped BigOperators
namespace DRGPR.GranularObservable
open FiniteController SupportedInformation GranularObservation GranularController
variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

/-- This estimator receives only the chosen identity and its numeric score. -/
def importance (p : FiniteController.Dist I) (a : I × ℝ) (j : I) : ℝ :=
  if a.1=j then a.2/p.val j else 0

/-- A universal recursion, independent of the environmental loss table. -/
def visibleState (η : ℝ) (initial : FiniteController.Dist I) :
    (n : ℕ) → Hist (I × ℝ) n → FiniteController.Dist I
  | 0, _ => initial
  | n+1, h =>
    let p := visibleState η initial n h.1
    update p (importance p h.2) η identityRows

def received (q : ℝ)
    (l : (n : ℕ) → Hist (I × (J → Bool)) n → I → J → ℝ) :
    (n : ℕ) → Hist (I × (J → Bool)) n → Hist (I × ℝ) n
  | 0, _ => ()
  | n+1, h => (received q l n h.1, (h.2.1, score q (l n h.1 h.2.1) h.2.2))

theorem estimate_from_received (q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1)
    (l : I → J → ℝ) (hl : ∀ i t, 0 ≤ l i t) (hl1 : ∀ i t, l i t ≤ 1)
    (p : FiniteController.Dist I) (a : I × (J → Bool)) :
    ((feedback q hq hq1 l hl hl1).round p).estimate a.1 a.2 =
      importance p (a.1,score q (l a.1) a.2) := by
  funext j
  simp [Feedback.round,feedback,RandomObservation.Round.estimate,
    RandomObservation.Round.usedScore,importance]

theorem state_factors_through_received (q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1)
    (η : ℝ) (hη : 0 < η) (initial : FiniteController.Dist I)
    (l : (n : ℕ) → Hist (I × (J → Bool)) n → I → J → ℝ)
    (hl : ∀ n h i t, 0 ≤ l n h i t) (hl1 : ∀ n h i t, l n h i t ≤ 1) :
    ∀ n h, (algorithm q hq hq1 η hη initial l hl hl1).state n h =
      visibleState η initial n (received q l n h) := by
  intro n
  induction n with
  | zero => intro h; rfl
  | succ n ih =>
    intro h
    change update ((algorithm q hq hq1 η hη initial l hl hl1).state n h.1)
      (((feedback q hq hq1 (l n h.1) (hl n h.1) (hl1 n h.1)).round
        ((algorithm q hq hq1 η hη initial l hl hl1).state n h.1)).estimate h.2.1 h.2.2)
      η identityRows = _
    rw [estimate_from_received,ih]
    rfl

/-- Two different hidden environments cannot alter the next sampling
distribution when the actual received histories agree. -/
theorem indistinguishable_received_histories (q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1)
    (η : ℝ) (hη : 0 < η) (initial : FiniteController.Dist I)
    (l g : (n : ℕ) → Hist (I × (J → Bool)) n → I → J → ℝ)
    (hl : ∀ n h i t, 0 ≤ l n h i t) (hl1 : ∀ n h i t, l n h i t ≤ 1)
    (hg : ∀ n h i t, 0 ≤ g n h i t) (hg1 : ∀ n h i t, g n h i t ≤ 1)
    (n : ℕ) (h h' : Hist (I × (J → Bool)) n)
    (heq : received q l n h = received q g n h') :
    (algorithm q hq hq1 η hη initial l hl hl1).state n h =
      (algorithm q hq hq1 η hη initial g hg hg1).state n h' := by
  rw [state_factors_through_received,state_factors_through_received,heq]

/-- A loss value at an erased coordinate does not affect the received score. -/
theorem erased_values_irrelevant (q : ℝ) (l g : J → ℝ) (mask : J → Bool)
    (hobs : ∀ t, mask t=false → l t=g t) : score q l mask = score q g mask := by
  apply Finset.sum_congr rfl
  intro t _
  cases hm : mask t
  · rw [hobs t hm]
  · simp [observed,hm]

/-- Changing an unselected policy has no effect on the received run score. -/
theorem unselected_values_irrelevant (q : ℝ) (l g : I → J → ℝ) (i : I)
    (mask : J → Bool) (hi : l i=g i) : score q (l i) mask=score q (g i) mask := by
  rw [hi]

end DRGPR.GranularObservable
#print axioms DRGPR.GranularObservable.estimate_from_received
#print axioms DRGPR.GranularObservable.state_factors_through_received
#print axioms DRGPR.GranularObservable.indistinguishable_received_histories
#print axioms DRGPR.GranularObservable.erased_values_irrelevant
#print axioms DRGPR.GranularObservable.unselected_values_irrelevant
