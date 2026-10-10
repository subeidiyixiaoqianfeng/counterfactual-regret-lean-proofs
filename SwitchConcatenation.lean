import ShortRunDistribution

noncomputable section
open scoped BigOperators
namespace DRGPR.SwitchConcatenation
variable {I : Type} [DecidableEq I]

def indicator (u : ℕ → I) (t : ℕ) : ℕ := if 0 < t ∧ u t ≠ u (t-1) then 1 else 0

theorem count_sum (u : ℕ → I) (n : ℕ) :
    (WindowLedger.switches u n).card=∑ t ∈ Finset.range n, indicator u t := by
  rw [Finset.card_eq_sum_ones]
  simp only [WindowLedger.switches,Finset.sum_filter,indicator]

theorem shifted_indicator (u : ℕ → I) (n t : ℕ) :
    indicator u (n+t)=indicator (fun r => u (n+r)) t + if t=0 then indicator u n else 0 := by
  by_cases ht : t=0
  · subst t; simp [indicator]
  · have hp : 0 < t := by omega
    have hnp : 0 < n+t := by omega
    have he : n+t-1=n+(t-1) := by omega
    simp [indicator,ht,hp,hnp,he]

/-- A concatenation has both internal counts and exactly one boundary
indicator when its suffix is nonempty. Time zero is never a switch. -/
theorem count_split (u : ℕ → I) (n m : ℕ) :
    (WindowLedger.switches u (n+m)).card=
      (WindowLedger.switches u n).card +
      (WindowLedger.switches (fun t => u (n+t)) m).card +
      if m=0 then 0 else indicator u n := by
  simp_rw [count_sum]
  rw [Finset.sum_range_add]
  simp_rw [shifted_indicator]
  rw [Finset.sum_add_distrib]
  have hz : (∑ t ∈ Finset.range m, if t=0 then indicator u n else 0)=
      if m=0 then 0 else indicator u n := by
    by_cases hm : m=0
    · simp [hm]
    · simp [hm,show 0 < m by omega]
  rw [hz]
  omega

/-- Nonempty concatenation expresses the boundary directly in the two
executed labels, not in the number of sampling or update operations. -/
theorem nonempty_count_split (u : ℕ → I) (n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    (WindowLedger.switches u (n+m)).card=
      (WindowLedger.switches u n).card +
      (WindowLedger.switches (fun t => u (n+t)) m).card +
      if u n=u (n-1) then 0 else 1 := by
  rw [count_split]
  simp [indicator,hn,show m ≠ 0 by omega]

def task (loss : ℕ → ℝ) (u : ℕ → I) (n : ℕ) : ℝ :=
  ((∑ t ∈ Finset.range n, loss t)+(WindowLedger.switches u n).card)/2

theorem task_split (loss : ℕ → ℝ) (u : ℕ → I) (n m : ℕ) :
    task loss u (n+m)=task loss u n+task (fun t => loss (n+t)) (fun t => u (n+t)) m+
      (if m=0 then 0 else (indicator u n:ℝ))/2 := by
  unfold task
  rw [Finset.sum_range_add,count_split]
  push_cast
  split_ifs <;> ring

end DRGPR.SwitchConcatenation
#print axioms DRGPR.SwitchConcatenation.count_sum
#print axioms DRGPR.SwitchConcatenation.shifted_indicator
#print axioms DRGPR.SwitchConcatenation.count_split
#print axioms DRGPR.SwitchConcatenation.nonempty_count_split
#print axioms DRGPR.SwitchConcatenation.task_split
