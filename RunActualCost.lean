import RunStateCoupling

noncomputable section
namespace DRGPR.RunActualCost
open SupportedInformation HistoryLookup SingleRunCoupling
variable {I : Type} [Fintype I] [DecidableEq I]

theorem lookup_project {E A : Type} (f : E → A) :
    ∀ n (h : Hist E n) (t : Fin n),
    lookup n (FiniteSimulation.project f n h) t=f (lookup n h t) := by
  intro n
  induction n with
  | zero => intro h t; exact Fin.elim0 t
  | succ n ih =>
    intro h t
    by_cases ht : t.val < n
    · change (if hlt : t.val < n then lookup n (FiniteSimulation.project f n h.1) ⟨t.val,hlt⟩ else f h.2)=_
      simp only [lookup,dif_pos ht]
      exact ih h.1 ⟨t.val,ht⟩
    · simp [lookup,FiniteSimulation.project,ht]

def labels (label : I → ℕ) (n : ℕ) (a : Hist (I × Bool) n) (t : ℕ) : ℕ :=
  if ht : t < n then label (lookup n a ⟨t,ht⟩).1 else 0

theorem held_label (label : I → ℕ) (i : I) (n : ℕ) (x : Hist Bool n) (t : ℕ) (ht : t < n) :
    labels label n (coins i n x) t=label i := by
  simp only [labels,dif_pos ht,coins,lookup_project]

theorem no_internal_switch (label : I → ℕ) (i : I) (n : ℕ) (x : Hist Bool n) :
    WindowLedger.switches (labels label n (coins i n x)) n=∅ := by
  apply Finset.eq_empty_iff_forall_not_mem.mpr
  intro t ht
  have hh := Finset.mem_filter.mp ht
  have hn := Finset.mem_range.mp hh.1
  have hp : t-1 < n := lt_of_le_of_lt (Nat.sub_le t 1) hn
  exact hh.2.2 (by rw [held_label label i n x t hn,held_label label i n x (t-1) hp])

def boundary (r : ℕ) (previous current : ℕ) : ℝ :=
  if r=0 then 0 else if previous=current then 0 else 1

def cost (label : I → ℕ) (r d previous : ℕ)
    (e : Hist (I → Bool) (d+1)) (a : Hist (I × Bool) (d+1)) : ℝ :=
  (ObliviousMinimax.learnerTotal (d+1) (ObliviousFactorization.zip (d+1) e a)+
    ((WindowLedger.switches (labels label (d+1) a) (d+1)).card:ℝ)+
    boundary r previous (labels label (d+1) a 0))/2

theorem held_cost (label : I → ℕ) (r d previous : ℕ) (i : I)
    (e : Hist (I → Bool) (d+1)) (x : Hist Bool (d+1)) :
    cost label r d previous e (coins i (d+1) x)=
      (ObliviousMinimax.tableTotal i (d+1) e+boundary r previous (label i))/2 := by
  unfold cost
  rw [RunStateCoupling.held_base_loss,no_internal_switch,held_label label i (d+1) x 0 (by omega)]
  simp

end DRGPR.RunActualCost
#print axioms DRGPR.RunActualCost.lookup_project
#print axioms DRGPR.RunActualCost.held_label
#print axioms DRGPR.RunActualCost.no_internal_switch
#print axioms DRGPR.RunActualCost.held_cost
