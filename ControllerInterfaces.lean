import FiniteController
import InterfaceCompletion

noncomputable section
open scoped BigOperators
namespace DRGPR.FiniteController
variable {I O : Type} [Fintype I] [Fintype O] [DecidableEq I]

def identityRows (i : I) : Dist I where
  val j := if i=j then 1 else 0
  nonneg j := by split_ifs <;> norm_num
  sum_one := by simp

def shareRows (α : ℝ) (hα : 0 ≤ α) (hα1 : α ≤ 1) (ν : Dist I) (i : I) : Dist I where
  val := InterfaceCompletion.share α ν.val i
  nonneg j := add_nonneg (mul_nonneg (sub_nonneg.mpr hα1) (by split_ifs <;> norm_num))
    (mul_nonneg hα (ν.nonneg j))
  sum_one := InterfaceCompletion.share_row_sum α ν.val ν.sum_one i

theorem normalized_tilt (p : Dist I) (z : I → ℝ) (η : ℝ) :
    (∑ i, p.val i*Real.exp (-η*z i)/normalizer p z η)=1 := by
  rw [← Finset.sum_div]
  exact div_self (normalizer_pos p z η).ne'

theorem share_update (p : Dist I) (z : I → ℝ) (η α : ℝ)
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (ν : Dist I) (j : I) :
    (update p z η (shareRows α hα hα1 ν)).val j =
      (1-α)*(p.val j*Real.exp (-η*z j)/normalizer p z η)+α*ν.val j := by
  have h := InterfaceCompletion.share_marginal α ν.val
    (fun i => p.val i*Real.exp (-η*z i)/normalizer p z η) (normalized_tilt p z η) j
  rw [← h]
  simp only [update, shareRows, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem newborn_exact_mass (p : Dist I) (z : I → ℝ) (η α : ℝ)
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (ν : Dist I) (j : I) (hnew : p.val j=0) :
    (update p z η (shareRows α hα hα1 ν)).val j=α*ν.val j := by
  rw [share_update, hnew]
  ring

theorem newborn_immediately_eligible (p : Dist I) (z : I → ℝ) (η α : ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1) (ν : Dist I) (j : I)
    (hnew : p.val j=0) (hν : 0 < ν.val j) :
    0 < (update p z η (shareRows α hα.le hα1 ν)).val j := by
  rw [newborn_exact_mass p z η α hα.le hα1 ν j hnew]
  exact mul_pos hα hν

theorem zero_update_retains_state (p : Dist I) (η : ℝ) :
    (update p (fun _ => 0) η identityRows).val=p.val := by
  funext j
  simp [update, identityRows, normalizer, p.sum_one]

theorem zero_duration_score (f : Feedback I O) (hd : f.d=0) (i : I) (o : O) :
    f.score i o=0 := le_antisymm (by simpa [hd] using f.score_le i o) (f.score_nonneg i o)

theorem zero_duration_estimate (f : Feedback I O) (p : Dist I) (hd : f.d=0) (i : I) (o : O) :
    (f.round p).estimate i o=(fun _ => 0) := by
  funext j
  simp [RandomObservation.Round.estimate, RandomObservation.Round.usedScore,
    Feedback.round, zero_duration_score f hd]

theorem zero_duration_loss (f : Feedback I O) (hd : f.d=0) (i : I) : f.loss i=0 := by
  have hm := f.moment i
  simp [zero_duration_score f hd] at hm
  exact hm.resolve_left (f.q_pos i).ne'

theorem padding_preserves_state (A : Program I O) (n : ℕ) (h : SupportedInformation.Hist (I × O) (n+1))
    (hd : (A.feedback n h.1).d=0) (ht : A.transition n h=identityRows) :
    (A.state (n+1) h).val=(A.state n h.1).val := by
  change (update (A.state n h.1) (((A.feedback n h.1).round (A.state n h.1)).estimate h.2.1 h.2.2)
    A.η (A.transition n h)).val=_
  rw [zero_duration_estimate _ _ hd, ht, zero_update_retains_state]

theorem padding_zero_contributions (A : Program I O)
    (v : (n : ℕ) → SupportedInformation.Hist (I × O) n → I)
    (n : ℕ) (h : SupportedInformation.Hist (I × O) n) (a : I × O)
    (hd : (A.feedback n h).d=0) :
    A.estimatedGap v n h a=0 ∧ A.actualGap v n h a=0 ∧ A.second n h a=0 := by
  simp [Program.estimatedGap, Program.actualGap, Program.second, Program.round,
    zero_duration_estimate _ _ hd, zero_duration_loss _ hd, DRGPR.mean]

theorem padding_zero_code (A : Program I O)
    (v : (n : ℕ) → SupportedInformation.Hist (I × O) n → I)
    (n : ℕ) (h : SupportedInformation.Hist (I × O) n) (a : I × O)
    (ht : A.transition n (h,a)=identityRows) (hv : v (n+1) (h,a)=v n h) :
    A.codeIncrement v n h a=0 := by
  simp [Program.codeIncrement, ht, hv, identityRows]

end DRGPR.FiniteController
#print axioms DRGPR.FiniteController.normalized_tilt
#print axioms DRGPR.FiniteController.share_update
#print axioms DRGPR.FiniteController.newborn_exact_mass
#print axioms DRGPR.FiniteController.newborn_immediately_eligible
#print axioms DRGPR.FiniteController.zero_update_retains_state
#print axioms DRGPR.FiniteController.zero_duration_score
#print axioms DRGPR.FiniteController.zero_duration_estimate
#print axioms DRGPR.FiniteController.zero_duration_loss
#print axioms DRGPR.FiniteController.padding_preserves_state
#print axioms DRGPR.FiniteController.padding_zero_contributions
#print axioms DRGPR.FiniteController.padding_zero_code
