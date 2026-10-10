import PhaseSchedule

noncomputable section
open scoped BigOperators
namespace DRGPR.HistoryLookup
open SupportedInformation PhaseSchedule

def lookup {E : Type} : (n : ℕ) → Hist E n → Fin n → E
  | 0, _, i => Fin.elim0 i
  | n+1, h, i => if hi : i.val < n then lookup n h.1 ⟨i.val,hi⟩ else h.2

theorem lookup_castSucc {E : Type} (n : ℕ) (h : Hist E (n+1)) (i : Fin n) :
    lookup (n+1) h i.castSucc=lookup n h.1 i := by simp [lookup,i.isLt]

theorem lookup_last {E : Type} (n : ℕ) (h : Hist E (n+1)) :
    lookup (n+1) h (Fin.last n)=h.2 := by simp [lookup]

theorem cumulative_lookup {E : Type} (c : ℕ → E → ℝ) :
    ∀ n (h : Hist E n), cumulative (fun r _ a => c r a) n h=
      ∑ r : Fin n, c r.val (lookup n h r) := by
  intro n
  induction n with
  | zero => intro h; simp [cumulative]
  | succ n ih =>
    intro h
    rw [Fin.sum_univ_castSucc]
    simp only [lookup_castSucc,lookup_last,Fin.coe_castSucc,Fin.val_last]
    exact congrArg (fun z => z+c n h.2) (ih h.1)

def runOf (T b : ℕ) (t : Fin T) : Fin T :=
  ⟨t.val/b,lt_of_le_of_lt (Nat.div_le_self _ _) t.isLt⟩

theorem regroup_runs {I : Type} (T b : ℕ) (choice : Fin T → I) (l : I → Fin T → ℝ) :
    (∑ r : Fin T, ∑ t ∈ slots T b r.val, l (choice r) t)=
      ∑ t, l (choice (runOf T b t)) t := by
  simp only [slots,Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  have he : ∀ r : Fin T, t.val/b=r.val ↔ r=runOf T b t := by
    intro r
    constructor
    · intro h; apply Fin.ext; exact h.symm
    · intro h; subst r; rfl
  simp only [he]
  simp

theorem constant_regroup {I : Type} (T b : ℕ) (j : I) (l : I → Fin T → ℝ) :
    (∑ r : Fin T, ∑ t ∈ slots T b r.val, l j t)=∑ t, l j t :=
  regroup_runs T b (fun _ => j) l

end DRGPR.HistoryLookup
#print axioms DRGPR.HistoryLookup.lookup_castSucc
#print axioms DRGPR.HistoryLookup.lookup_last
#print axioms DRGPR.HistoryLookup.cumulative_lookup
#print axioms DRGPR.HistoryLookup.regroup_runs
#print axioms DRGPR.HistoryLookup.constant_regroup
