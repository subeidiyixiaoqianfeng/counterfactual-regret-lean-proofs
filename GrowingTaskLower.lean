import GrowingTableReduction
import TaskSaturation

noncomputable section
open scoped BigOperators
namespace DRGPR.GrowingTaskLower
open DependentBlocks GrowingInformation GrowingTableReduction
open MultiphaseOblivious (Table Coins Environment)
variable {K : ℕ → ℕ} {n : ℕ}

def labels (r : ℕ) (a : Coins (Fin (K r)) n) (t : ℕ) : ℕ :=
  if ht : t < n then (HistoryLookup.lookup n a ⟨t,ht⟩).1.val else 0

def boundary : (r : ℕ) → History (fun s => Coins (Fin (K s)) n) r → Coins (Fin (K r)) n → ℝ
  | 0, _, _ => 0
  | r+1, h, a => if labels r h.2 (n-1)=labels (r+1) a 0 then 0 else 1

def switchStep (r : ℕ) (h : History (fun s => Coins (Fin (K s)) n) r)
    (a : Coins (Fin (K r)) n) : ℝ :=
  ((WindowLedger.switches (labels r a) n).card:ℝ)+boundary r h a

theorem switch_step_bounds (r : ℕ) (h : History (fun s => Coins (Fin (K s)) n) r)
    (a : Coins (Fin (K r)) n) : 0 ≤ switchStep r h a ∧ switchStep r h a ≤ (n:ℝ)+1 := by
  have hb : 0 ≤ boundary r h a ∧ boundary r h a ≤ 1 := by
    cases r with
    | zero => simp [boundary]
    | succ r =>
      change 0 ≤ (if labels r h.2 (n-1)=labels (r+1) a 0 then (0:ℝ) else 1) ∧
        (if labels r h.2 (n-1)=labels (r+1) a 0 then (0:ℝ) else 1) ≤ 1
      split_ifs <;> norm_num
  have hc : ((WindowLedger.switches (labels r a) n).card:ℝ) ≤ n := by
    exact_mod_cast (TaskSaturation.internal_switch_count (labels r a) n).trans (Nat.sub_le n 1)
  have hz : (0:ℝ) ≤ (WindowLedger.switches (labels r a) n).card := Nat.cast_nonneg _
  unfold switchStep
  constructor <;> linarith

theorem switches_bounds : ∀ m (a : History (fun r => Coins (Fin (K r)) n) m),
    0 ≤ total switchStep m a ∧ total switchStep m a ≤ (m:ℝ)*((n:ℝ)+1) := by
  intro m
  induction m with
  | zero => intro a; simp [total]
  | succ m ih =>
    intro a
    have hp := ih a.1
    have hs := switch_step_bounds m a.1 a.2
    simp only [total,Nat.cast_add,Nat.cast_one]
    constructor <;> nlinarith

def taskCost (m : ℕ) (e : History (fun r => Table (Fin (K r)) n) m)
    (a : History (fun r => Coins (Fin (K r)) n) m) : ℝ :=
  (played m e a+total switchStep m a)/2

theorem task_bounds (m : ℕ) (e : History (fun r => Table (Fin (K r)) n) m) a :
    played m e a/2 ≤ taskCost m e a ∧ taskCost m e a ≤ (m:ℝ)*((n:ℝ)+1) := by
  have hp := played_bounds m e a
  have hs := switches_bounds m a
  unfold taskCost
  have hm : (0:ℝ) ≤ m := Nat.cast_nonneg _
  constructor <;> nlinarith

def comparatorSwitch : (r : ℕ) → History (fun s => Fin (K s)) r → Fin (K r) → ℝ
  | 0, _, _ => 0
  | r+1, h, i => if h.2.val=i.val then 0 else 1

theorem comparator_switch_bounds (r : ℕ) (h : History (fun s => Fin (K s)) r) (i : Fin (K r)) :
    0 ≤ comparatorSwitch r h i ∧ comparatorSwitch r h i ≤ 1 := by
  cases r with
  | zero => simp [comparatorSwitch]
  | succ r =>
    change 0 ≤ (if h.2.val=i.val then (0:ℝ) else 1) ∧ (if h.2.val=i.val then (0:ℝ) else 1) ≤ 1
    split_ifs <;> norm_num

def comparatorCost : (m : ℕ) → History (fun r => Table (Fin (K r)) n) m →
    History (fun r => Fin (K r)) m → ℝ
  | 0, _, _ => 0
  | m+1, e, v => comparatorCost m e.1 v.1+
      (ObliviousMinimax.tableTotal v.2 n e.2+comparatorSwitch m v.1 v.2)/2

def targetPath (m : ℕ) := DependentFactorization.project
  (fun r (e : Environment (Fin (K r)) n) => e.1) m

theorem comparator_nonneg : ∀ m (e : History (fun r => Table (Fin (K r)) n) m) v,
    0 ≤ comparatorCost m e v := by
  intro m
  induction m with
  | zero => intro e v; exact le_rfl
  | succ m ih =>
    intro e v
    have hb := ObliviousMinimax.total_bounds
      (fun x : Fin (K m) → Bool => ObliviousInformation.loss (x v.2))
      (fun _ => ObliviousMinimax.loss_bounds _) n e.2
    have hs := comparator_switch_bounds m v.1 v.2
    change 0 ≤ ObliviousMinimax.tableTotal v.2 n e.2 ∧ _ at hb
    change 0 ≤ comparatorCost m e.1 v.1+_/2
    have hi := ih e.1 v.1
    linarith

theorem target_cost_upper : ∀ m (e : History (fun r => Environment (Fin (K r)) n) m),
    comparatorCost m (tables m e) (targetPath m e) ≤ targetTotal m e/2+(m:ℝ)/2 := by
  intro m
  induction m with
  | zero => intro e; simp [comparatorCost,targetTotal,total]
  | succ m ih =>
    intro e
    have hp := ih e.1
    have hs := comparator_switch_bounds m (targetPath m e.1) e.2.1
    change comparatorCost m (tables m e.1) (targetPath m e.1)+
      (ObliviousMinimax.tableTotal e.2.1 n e.2.2+comparatorSwitch m (targetPath m e.1) e.2.1)/2 ≤
      (targetTotal m e.1+ObliviousMinimax.tableTotal e.2.1 n e.2.2)/2+((m+1:ℕ):ℝ)/2
    push_cast
    linarith

def fixedTask (A : Master K n) (q : ℝ) (m : ℕ)
    (e : History (fun r => Environment (Fin (K r)) n) m) : ℝ :=
  ∑ a, DependentFactorization.weight (response A q) m e a*taskCost m (tables m e) a

theorem fixed_task_ignores_targets (A : Master K n) (q : ℝ) (m : ℕ)
    (e e' : History (fun r => Environment (Fin (K r)) n) m) (he : tables m e=tables m e') :
    fixedTask A q m e=fixedTask A q m e' := by
  unfold fixedTask
  apply Finset.sum_congr rfl
  intro a _
  rw [weight_ignores_targets A q m e e' a he,he]

theorem fixed_task_bounds (A : Master K n) (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (m : ℕ) (e : History (fun r => Environment (Fin (K r)) n) m) :
    fixedLoss A q m e/2 ≤ fixedTask A q m e ∧ fixedTask A q m e ≤ (m:ℝ)*((n:ℝ)+1) := by
  have hw := DependentFactorization.weight_nonneg _ (response_nonneg A q hq hq1) m e
  have hn := DependentFactorization.normalized _ (response_normalized A q) m e
  constructor
  · unfold fixedLoss fixedTask
    rw [Finset.sum_div]
    apply Finset.sum_le_sum
    intro a _
    have h := mul_le_mul_of_nonneg_left (task_bounds m (tables m e) a).1 (hw a)
    simpa only [← mul_div_assoc] using h
  · calc
      _ ≤ ∑ a, DependentFactorization.weight (response A q) m e a*((m:ℝ)*((n:ℝ)+1)) :=
        Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (task_bounds m (tables m e) a).2 (hw a))
      _ = _ := by rw [← Finset.sum_mul,hn,one_mul]

def best (m : ℕ) (e : History (fun r => Table (Fin (K r)) n) m) : ℝ :=
  sInf (Set.range (comparatorCost m e))

def regret (hK : ∀ r, 2 ≤ K r) (A : Master K n) (q : ℝ) (m : ℕ)
    (e : History (fun r => Table (Fin (K r)) n) m) : ℝ :=
  fixedTask A q m (liftTables hK m e)-best m e

theorem best_le (m : ℕ) (e : History (fun r => Table (Fin (K r)) n) m) v :
    best m e ≤ comparatorCost m e v :=
  csInf_le ⟨0,by rintro _ ⟨w,rfl⟩; exact comparator_nonneg m e w⟩ ⟨v,rfl⟩

theorem best_nonneg (hK : ∀ r, 2 ≤ K r) (m : ℕ) (e : History (fun r => Table (Fin (K r)) n) m) :
    0 ≤ best m e := by
  letI : Nonempty (History (fun r => Fin (K r)) m) := ⟨targetPath m (defaultEnvironment (n:=n) hK m)⟩
  apply le_csInf (Set.range_nonempty _)
  rintro _ ⟨v,rfl⟩
  exact comparator_nonneg m e v

/-- The learner pays its actual switching cost. The comparator pays its own
phase switches. Target labels are eliminated before the fixed table is returned. -/
theorem fixed_table_lower (A : Master K n) (q : ℝ) (m : ℕ) (hn : 0 < n)
    (hK : ∀ r, 2 ≤ K r) (hq : 0 < q) (hq1 : q ≤ 1) :
    ∃ e : History (fun r => Table (Fin (K r)) n) m,
      (∑ r ∈ Finset.range m, lower K n q r)/2-(m:ℝ)/2 ≤ regret hK A q m e := by
  obtain ⟨e,he⟩ := exists_fixed_table A q m hn hK hq hq1
  rw [fixed_gap_identity] at he
  refine ⟨tables m e,?_⟩
  have hl := (fixed_task_bounds A q hq.le hq1 m e).1
  have hc := target_cost_upper m e
  have hb := best_le m (tables m e) (targetPath m e)
  have hsame := fixed_task_ignores_targets A q m e (liftTables hK m (tables m e)) (by rw [tables_lift])
  unfold regret
  rw [← hsame]
  linarith

theorem regret_upper (hK : ∀ r, 2 ≤ K r) (A : Master K n) (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (m : ℕ) (e : History (fun r => Table (Fin (K r)) n) m) :
    regret hK A q m e ≤ (m:ℝ)*((n:ℝ)+1) := by
  have hl := (fixed_task_bounds A q hq hq1 m (liftTables hK m e)).2
  have hb := best_nonneg hK m e
  unfold regret
  linarith

def worst (hK : ∀ r, 2 ≤ K r) (A : Master K n) (q : ℝ) (m : ℕ) : ℝ :=
  sSup (Set.range (regret hK A q m))
def minimax (hK : ∀ r, 2 ≤ K r) (q : ℝ) (n m : ℕ) : ℝ :=
  sInf (Set.range (fun A : Master K n => worst hK A q m))

theorem minimax_lower (q : ℝ) (n m : ℕ) (hn : 0 < n)
    (hK : ∀ r, 2 ≤ K r) (hq : 0 < q) (hq1 : q ≤ 1) :
    (∑ r ∈ Finset.range m, lower K n q r)/2-(m:ℝ)/2 ≤ minimax hK q n m := by
  letI : Nonempty (Master K n) :=
    ⟨⟨fun r _ => ObliviousMinimax.constantAlgorithm ⟨0,by have := hK r; omega⟩⟩⟩
  apply le_csInf (Set.range_nonempty _)
  rintro _ ⟨A,rfl⟩
  obtain ⟨e,he⟩ := fixed_table_lower A q m hn hK hq hq1
  apply he.trans
  apply le_csSup
  · refine ⟨(m:ℝ)*((n:ℝ)+1),?_⟩
    rintro _ ⟨e,rfl⟩
    exact regret_upper hK A q hq.le hq1 m e
  · exact ⟨e,rfl⟩

end DRGPR.GrowingTaskLower
#print axioms DRGPR.GrowingTaskLower.switch_step_bounds
#print axioms DRGPR.GrowingTaskLower.switches_bounds
#print axioms DRGPR.GrowingTaskLower.task_bounds
#print axioms DRGPR.GrowingTaskLower.comparator_switch_bounds
#print axioms DRGPR.GrowingTaskLower.comparator_nonneg
#print axioms DRGPR.GrowingTaskLower.target_cost_upper
#print axioms DRGPR.GrowingTaskLower.fixed_task_ignores_targets
#print axioms DRGPR.GrowingTaskLower.fixed_task_bounds
#print axioms DRGPR.GrowingTaskLower.best_le
#print axioms DRGPR.GrowingTaskLower.best_nonneg
#print axioms DRGPR.GrowingTaskLower.fixed_table_lower
#print axioms DRGPR.GrowingTaskLower.regret_upper
#print axioms DRGPR.GrowingTaskLower.minimax_lower
