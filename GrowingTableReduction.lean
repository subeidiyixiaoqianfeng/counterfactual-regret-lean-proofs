import GrowingInformation

noncomputable section
open scoped BigOperators
namespace DRGPR.GrowingTableReduction
open DependentBlocks GrowingInformation
open MultiphaseOblivious (Table Coins Transcript Environment Block)
variable {K : ℕ → ℕ} {n : ℕ}

def tables (m : ℕ) := DependentFactorization.project
  (fun r (e : Environment (Fin (K r)) n) => e.2) m

def liftTables (hK : ∀ r, 2 ≤ K r) (m : ℕ) := DependentFactorization.project
  (fun r (t : Table (Fin (K r)) n) => ((⟨0,by have := hK r; omega⟩ : Fin (K r)),t)) m

theorem tables_lift (hK : ∀ r, 2 ≤ K r) : ∀ m (e : History (fun r => Table (Fin (K r)) n) m),
    tables m (liftTables hK m e)=e := by
  intro m
  induction m with
  | zero => intro e; cases e; rfl
  | succ m ih => intro e; change (tables m (liftTables hK m e.1),e.2)=e; rw [ih]; rfl

theorem visible_ignores_targets :
    ∀ m (e e' : History (fun r => Environment (Fin (K r)) n) m)
      (a : History (fun r => Coins (Fin (K r)) n) m), tables m e=tables m e' →
      DependentFactorization.project visible m (DependentFactorization.zip m e a)=
      DependentFactorization.project visible m (DependentFactorization.zip m e' a) := by
  intro m
  induction m with
  | zero => intro e e' a he; rfl
  | succ m ih =>
    intro e e' a he
    change (tables m e.1,e.2.2)=(tables m e'.1,e'.2.2) at he
    have hp := congrArg Prod.fst he
    have hl := congrArg Prod.snd he
    change (DependentFactorization.project visible m (DependentFactorization.zip m e.1 a.1),
      MultiphaseOblivious.visibleBlock n (e.2,a.2)) =
      (DependentFactorization.project visible m (DependentFactorization.zip m e'.1 a.1),
      MultiphaseOblivious.visibleBlock n (e'.2,a.2))
    rw [ih _ _ _ hp]
    unfold MultiphaseOblivious.visibleBlock
    dsimp only
    rw [hl]

theorem weight_ignores_targets (A : Master K n) (q : ℝ) :
    ∀ m (e e' : History (fun r => Environment (Fin (K r)) n) m)
      (a : History (fun r => Coins (Fin (K r)) n) m), tables m e=tables m e' →
      DependentFactorization.weight (response A q) m e a=
      DependentFactorization.weight (response A q) m e' a := by
  intro m
  induction m with
  | zero => intro e e' a he; rfl
  | succ m ih =>
    intro e e' a he
    change (tables m e.1,e.2.2)=(tables m e'.1,e'.2.2) at he
    have hp := congrArg Prod.fst he
    have hl := congrArg Prod.snd he
    change DependentFactorization.weight (response A q) m e.1 a.1 *
      ObliviousFactorization.playerWeight (ObliviousInformation.choice
        (A.policy m (DependentFactorization.project visible m (DependentFactorization.zip m e.1 a.1))).p q) n e.2.2 a.2 =
      DependentFactorization.weight (response A q) m e'.1 a.1 *
      ObliviousFactorization.playerWeight (ObliviousInformation.choice
        (A.policy m (DependentFactorization.project visible m (DependentFactorization.zip m e'.1 a.1))).p q) n e'.2.2 a.2
    rw [ih _ _ _ hp,visible_ignores_targets m e.1 e'.1 a.1 hp,hl]

def played : (m : ℕ) → History (fun r => Table (Fin (K r)) n) m →
    History (fun r => Coins (Fin (K r)) n) m → ℝ
  | 0, _, _ => 0
  | m+1, e, a => played m e.1 a.1+
      ObliviousMinimax.learnerTotal n (ObliviousFactorization.zip n e.2 a.2)

def targetTotal := @total (fun r => Environment (Fin (K r)) n)
  (fun _ _ e => ObliviousMinimax.tableTotal e.1 n e.2)

def fixedLoss (A : Master K n) (q : ℝ) (m : ℕ)
    (e : History (fun r => Environment (Fin (K r)) n) m) : ℝ :=
  ∑ a, DependentFactorization.weight (response A q) m e a*played m (tables m e) a

theorem total_gap_identity : ∀ m (e : History (fun r => Environment (Fin (K r)) n) m) a,
    total cost m (DependentFactorization.zip m e a)=played m (tables m e) a-targetTotal m e := by
  intro m
  induction m with
  | zero => intro e a; simp [total,played,targetTotal]
  | succ m ih =>
    intro e a
    change total cost m (DependentFactorization.zip m e.1 a.1)+
      (ObliviousMinimax.learnerTotal n (ObliviousFactorization.zip n e.2.2 a.2)-
        ObliviousMinimax.tableTotal e.2.1 n e.2.2)=
      (played m (tables m e.1) a.1+ObliviousMinimax.learnerTotal n (ObliviousFactorization.zip n e.2.2 a.2))-
      (targetTotal m e.1+ObliviousMinimax.tableTotal e.2.1 n e.2.2)
    rw [ih]
    ring

theorem fixed_gap_identity (A : Master K n) (q : ℝ) (m : ℕ)
    (e : History (fun r => Environment (Fin (K r)) n) m) :
    fixedGap A q m e=fixedLoss A q m e-targetTotal m e := by
  unfold fixedGap
  simp_rw [total_gap_identity,mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul,
    DependentFactorization.normalized _ (response_normalized A q),one_mul]
  rfl

theorem played_bounds : ∀ m (e : History (fun r => Table (Fin (K r)) n) m) a,
    0 ≤ played m e a ∧ played m e a ≤ (m:ℝ)*(n:ℝ) := by
  intro m
  induction m with
  | zero => intro e a; simp [played]
  | succ m ih =>
    intro e a
    have hp := ih e.1 a.1
    have hb := ObliviousMinimax.total_bounds
      (fun x : ObliviousInformation.Event (Fin (K m)) => ObliviousInformation.loss (x.1 x.2.1))
      (fun _ => ObliviousMinimax.loss_bounds _) n (ObliviousFactorization.zip n e.2 a.2)
    change 0 ≤ ObliviousMinimax.learnerTotal n (ObliviousFactorization.zip n e.2 a.2) ∧
      ObliviousMinimax.learnerTotal n (ObliviousFactorization.zip n e.2 a.2) ≤ (n:ℝ) at hb
    simp only [played,Nat.cast_add,Nat.cast_one]
    constructor <;> nlinarith

end DRGPR.GrowingTableReduction
#print axioms DRGPR.GrowingTableReduction.tables_lift
#print axioms DRGPR.GrowingTableReduction.visible_ignores_targets
#print axioms DRGPR.GrowingTableReduction.weight_ignores_targets
#print axioms DRGPR.GrowingTableReduction.total_gap_identity
#print axioms DRGPR.GrowingTableReduction.fixed_gap_identity
#print axioms DRGPR.GrowingTableReduction.played_bounds
