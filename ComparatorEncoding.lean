import GrowingTaskLower

noncomputable section
open scoped BigOperators
namespace DRGPR.ComparatorEncoding
open DependentBlocks
variable {E : ℕ → Type}

def takePath (v : (r : ℕ) → E r) : (m : ℕ) → History E m
  | 0 => ()
  | m+1 => (takePath v m,v m)

theorem prefix_congr (v w : (r : ℕ) → E r) : ∀ m,
    (∀ r, r < m → v r=w r) → takePath v m=takePath w m := by
  intro m
  induction m with
  | zero => intro _; rfl
  | succ m ih =>
    intro h
    change (takePath v m,v m)=(takePath w m,w m)
    rw [ih (fun r hr => h r (by omega)),h m (by omega)]

def overwrite (v : (r : ℕ) → E r) (m : ℕ) (x : E m) (r : ℕ) : E r :=
  if h : r=m then h.symm ▸ x else v r

theorem overwrite_at (v : (r : ℕ) → E r) (m : ℕ) (x : E m) : overwrite v m x m=x := by
  simp [overwrite]

theorem overwrite_prefix (v : (r : ℕ) → E r) (m : ℕ) (x : E m) :
    takePath (overwrite v m x) m=takePath v m := by
  apply prefix_congr
  intro r hr
  simp [overwrite,show r ≠ m by omega]

/-- Infinite schedules and finite growing-type paths describe the same
finite-horizon comparator choices. No future choice gives extra information. -/
theorem prefix_surjective (fallback : (r : ℕ) → E r) :
    ∀ m, Function.Surjective (fun v : (r : ℕ) → E r => takePath v m) := by
  intro m
  induction m with
  | zero => intro h; cases h; exact ⟨fallback,rfl⟩
  | succ m ih =>
    intro h
    obtain ⟨v,hv⟩ := ih h.1
    change takePath v m=h.1 at hv
    refine ⟨overwrite v m h.2,?_⟩
    change (takePath (overwrite v m h.2) m,overwrite v m h.2 m)=h
    rw [overwrite_prefix,overwrite_at,hv]
    rfl

theorem prefix_cost_range (fallback : (r : ℕ) → E r) (m : ℕ)
    (c : History E m → ℝ) :
    Set.range (fun v => c (takePath v m))=Set.range c := by
  ext z
  constructor
  · rintro ⟨v,rfl⟩
    exact ⟨takePath v m,rfl⟩
  · rintro ⟨h,rfl⟩
    obtain ⟨v,hv⟩ := prefix_surjective fallback m h
    exact ⟨v,congrArg c hv⟩

theorem table_total_sum {I : Type} (i : I) : ∀ n (e : SupportedInformation.Hist (I → Bool) n),
    ObliviousMinimax.tableTotal i n e=
      ∑ t : Fin n, ObliviousInformation.loss (HistoryLookup.lookup n e t i) := by
  intro n
  induction n with
  | zero => intro e; simp [ObliviousMinimax.tableTotal,SupportedInformation.cumulative]
  | succ n ih =>
    intro e
    rw [Fin.sum_univ_castSucc]
    simp only [HistoryLookup.lookup_castSucc,HistoryLookup.lookup_last]
    change ObliviousMinimax.tableTotal i n e.1+ObliviousInformation.loss (e.2 i)=_
    rw [ih]

namespace Model
variable (M : RestartedGrowing.Model)
variable (tables : (r : ℕ) → MultiphaseOblivious.Table (Fin (M.K r)) M.n)
variable (hl : ∀ r i t, M.loss r i t=
  ObliviousInformation.loss (HistoryLookup.lookup M.n (tables r) t i))

include hl

theorem base_cost (r : ℕ) (i : Fin (M.K r)) :
    M.baseComparator r i=ObliviousMinimax.tableTotal i M.n (tables r)/2 := by
  unfold RestartedGrowing.Model.baseComparator PhaseAlgorithm.comparatorTotal
  rw [table_total_sum]
  simp_rw [hl]

omit hl in
theorem switch_cost (v : (r : ℕ) → Fin (M.K r)) (m : ℕ) :
    M.comparatorSwitch v m=GrowingTaskLower.comparatorSwitch m (takePath v m) (v m) := by
  cases m <;> rfl

/-- Both encodings charge the comparator its own task loss and its own
cross-phase switches, with the identical factor of one half. -/
theorem cost_exact (v : (r : ℕ) → Fin (M.K r)) : ∀ m,
    M.comparatorCost v m=GrowingTaskLower.comparatorCost m (takePath tables m) (takePath v m) := by
  intro m
  induction m with
  | zero => simp [RestartedGrowing.Model.comparatorCost,GrowingTaskLower.comparatorCost]
  | succ m ih =>
    change (∑ r ∈ Finset.range (m+1),
      (M.baseComparator r (v r)+M.comparatorSwitch v r/2))=_
    rw [Finset.sum_range_succ]
    change M.comparatorCost v m+(M.baseComparator m (v m)+M.comparatorSwitch v m/2)=_
    rw [ih,base_cost M tables hl,switch_cost]
    change _=GrowingTaskLower.comparatorCost m (takePath tables m) (takePath v m)+
      (ObliviousMinimax.tableTotal (v m) M.n (tables m)+
        GrowingTaskLower.comparatorSwitch m (takePath v m) (v m))/2
    ring

theorem cost_range_exact (m : ℕ) :
    Set.range (fun v => M.comparatorCost v m)=
      Set.range (GrowingTaskLower.comparatorCost m (takePath tables m)) := by
  simp_rw [cost_exact M tables hl]
  exact prefix_cost_range M.fallback m _

theorem best_exact (m : ℕ) :
    sInf (Set.range (fun v => M.comparatorCost v m))=
      GrowingTaskLower.best m (takePath tables m) := by
  rw [cost_range_exact M tables hl]
  rfl

end Model
end DRGPR.ComparatorEncoding
#print axioms DRGPR.ComparatorEncoding.prefix_congr
#print axioms DRGPR.ComparatorEncoding.overwrite_at
#print axioms DRGPR.ComparatorEncoding.overwrite_prefix
#print axioms DRGPR.ComparatorEncoding.prefix_surjective
#print axioms DRGPR.ComparatorEncoding.prefix_cost_range
#print axioms DRGPR.ComparatorEncoding.table_total_sum
#print axioms DRGPR.ComparatorEncoding.Model.base_cost
#print axioms DRGPR.ComparatorEncoding.Model.switch_cost
#print axioms DRGPR.ComparatorEncoding.Model.cost_exact
#print axioms DRGPR.ComparatorEncoding.Model.cost_range_exact
#print axioms DRGPR.ComparatorEncoding.Model.best_exact
