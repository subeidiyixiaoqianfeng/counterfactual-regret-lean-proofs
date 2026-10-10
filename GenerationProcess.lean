import SupportedInformation
import InterfaceCompletion

noncomputable section
open scoped BigOperators
namespace DRGPR.GenerationProcess
open SupportedInformation
variable {I : Type} [Fintype I] [DecidableEq I]

def missed (target : I) : (n : ℕ) → Hist I n → Bool
  | 0, _ => true
  | n+1, h => missed target n h.1 && decide (h.2 ≠ target)

def failure (k : (n : ℕ) → Hist I n → I → ℝ) (target : I) (n : ℕ) : ℝ :=
  ∑ h, pathLaw k n h * (if missed target n h then 1 else 0)

theorem failure_nonneg (k : (n : ℕ) → Hist I n → I → ℝ)
    (hk : ∀ n h i, 0 ≤ k n h i) (target : I) (n : ℕ) : 0 ≤ failure k target n := by
  apply Finset.sum_nonneg
  intro h _
  exact mul_nonneg (pathLaw_nonneg k hk n h) (by split_ifs <;> norm_num)

theorem failure_step (k : (n : ℕ) → Hist I n → I → ℝ)
    (hk : ∀ n h i, 0 ≤ k n h i) (hks : ∀ n h, ∑ i, k n h i=1)
    (target : I) (rate : ℝ) (hit : ∀ n h, rate ≤ k n h target) (n : ℕ) :
    failure k target (n+1) ≤ (1-rate)*failure k target n := by
  unfold failure
  change (∑ h : Hist I n × I, (pathLaw k n h.1*k n h.1 h.2)*
    (if missed target n h.1 && decide (h.2 ≠ target) then 1 else 0)) ≤ _
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro h _
  by_cases hm : missed target n h=true
  · simp only [hm, Bool.true_and, Bool.decide_coe]
    have he : (∑ i, k n h i * (if i ≠ target then (1:ℝ) else 0))=1-k n h target := by
      have hsum : (∑ i, k n h i)=
          (∑ i, k n h i*(if i ≠ target then (1:ℝ) else 0))+k n h target := by
        calc
          _ = ∑ i, (k n h i*(if i ≠ target then (1:ℝ) else 0)+
              (if i=target then k n h i else 0)) := by
                apply Finset.sum_congr rfl
                intro i _
                by_cases ht : i=target <;> simp [ht]
          _ = _ := by simp [Finset.sum_add_distrib]
      linarith [hks n h]
    simp only [mul_assoc, ← Finset.mul_sum]
    simp only [decide_eq_true_eq, if_true, mul_one]
    rw [he]
    nlinarith [pathLaw_nonneg k hk n h,hit n h]
  · have hm0 : missed target n h=false := Bool.eq_false_iff.mpr hm
    simp [hm0]

theorem failure_bound (k : (n : ℕ) → Hist I n → I → ℝ)
    (hk : ∀ n h i, 0 ≤ k n h i) (hks : ∀ n h, ∑ i, k n h i=1)
    (target : I) (rate : ℝ) (hrate : rate ≤ 1) (hit : ∀ n h, rate ≤ k n h target) :
    ∀ n, failure k target n ≤ (1-rate)^n := by
  intro n
  induction n with
  | zero => simp [failure, Hist, pathLaw, missed]
  | succ n ih =>
    have hh := mul_le_mul_of_nonneg_left ih (sub_nonneg.mpr hrate)
    simpa [pow_succ, mul_comm] using le_trans (failure_step k hk hks target rate hit n) hh

theorem expected_delay_loss (k : (n : ℕ) → Hist I n → I → ℝ)
    (hk : ∀ n h i, 0 ≤ k n h i) (hks : ∀ n h, ∑ i, k n h i=1)
    (target : I) (rate : ℝ) (hrate : rate ≤ 1) (hit : ∀ n h, rate ≤ k n h target)
    (n T a : ℕ) (lossGap : Hist I n → ℝ)
    (hgap : ∀ h, lossGap h ≤ (a:ℝ)+(T:ℝ)*(if missed target n h then 1 else 0)) :
    (∑ h, pathLaw k n h*lossGap h) ≤ (a:ℝ)+(T:ℝ)*(1-rate)^n := by
  have hi := Finset.sum_le_sum (fun h (_ : h ∈ (Finset.univ : Finset (Hist I n))) =>
    mul_le_mul_of_nonneg_left (hgap h) (pathLaw_nonneg k hk n h))
  have he : (∑ h, pathLaw k n h*((a:ℝ)+(T:ℝ)*(if missed target n h then 1 else 0))) =
      (a:ℝ)+(T:ℝ)*failure k target n := by
    simp only [mul_add, Finset.sum_add_distrib]
    rw [← Finset.sum_mul, pathLaw_normalized k hks, one_mul]
    congr 1
    unfold failure
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h _
    ring
  rw [he] at hi
  have hb := mul_le_mul_of_nonneg_left (failure_bound k hk hks target rate hrate hit n) (Nat.cast_nonneg T)
  linarith

theorem mutually_exclusive_hazards (p : I → ℝ) (rate : ℝ)
    (hpsum : ∑ i, p i=1) (hhit : ∀ i, rate ≤ p i) :
    (Fintype.card I:ℝ)*rate ≤ 1 := by
  have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset I)) => hhit i)
  simpa [hpsum] using h

theorem budget_attempts (B m : ℕ) : m*(B/m) ≤ B := Nat.mul_div_le B m

def spent (budget cost : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | n+1 => let old := spent budget cost n
    if old+cost n ≤ budget (n+1) then old+cost n else old

theorem admission_hard_feasible (budget cost : ℕ → ℝ)
    (hb0 : 0 ≤ budget 0) (hmono : ∀ n, budget n ≤ budget (n+1)) :
    ∀ n, spent budget cost n ≤ budget n := by
  intro n
  induction n with
  | zero => exact hb0
  | succ n ih =>
    simp only [spent]
    split_ifs with h
    · exact h
    · exact le_trans ih (hmono n)

end DRGPR.GenerationProcess
#print axioms DRGPR.GenerationProcess.failure_nonneg
#print axioms DRGPR.GenerationProcess.failure_step
#print axioms DRGPR.GenerationProcess.failure_bound
#print axioms DRGPR.GenerationProcess.expected_delay_loss
#print axioms DRGPR.GenerationProcess.mutually_exclusive_hazards
#print axioms DRGPR.GenerationProcess.budget_attempts
#print axioms DRGPR.GenerationProcess.admission_hard_feasible
