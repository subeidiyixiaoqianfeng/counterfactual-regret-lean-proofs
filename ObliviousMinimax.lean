import ObliviousInformation

noncomputable section
open scoped BigOperators
namespace DRGPR.ObliviousMinimax
open SupportedInformation ObliviousInformation ObliviousFactorization
variable {I : Type} [Fintype I] [DecidableEq I]

structure Algorithm (I : Type) [Fintype I] where
  p : (n : ℕ) → Hist (I × Option Bool) n → I → ℝ
  nonneg : ∀ n h i, 0 ≤ p n h i
  normalized : ∀ n h, ∑ i, p n h i=1

def constantAlgorithm (i : I) : Algorithm I where
  p _ _ j := if i=j then 1 else 0
  nonneg _ _ _ := by split_ifs <;> norm_num
  normalized _ _ := by simp

def learnerTotal : (n : ℕ) → Hist (Event I) n → ℝ :=
  cumulative (fun _ _ x => loss (x.1 x.2.1))
def tableTotal (j : I) : (n : ℕ) → Hist (I → Bool) n → ℝ :=
  cumulative (fun _ _ row => loss (row j))
def fixedLearner (A : Algorithm I) (q : ℝ) (N : ℕ) (table : Hist (I → Bool) N) : ℝ :=
  ∑ a, playerWeight (choice A.p q) N table a*learnerTotal N (zip N table a)
def regret (A : Algorithm I) (q : ℝ) (N : ℕ) (table : Hist (I → Bool) N) : ℝ :=
  fixedLearner A q N table-sInf (Set.range (fun j => tableTotal j N table))
def worst (A : Algorithm I) (q : ℝ) (N : ℕ) : ℝ :=
  sSup (Set.range (regret A q N))
def minimax (q : ℝ) (N : ℕ) : ℝ := sInf (Set.range (fun A : Algorithm I => worst A q N))

theorem loss_bounds (b : Bool) : 0 ≤ loss b ∧ loss b ≤ 1 := by
  cases b <;> norm_num [loss]

theorem total_bounds {X : Type} (cost : X → ℝ) (hc : ∀ x, 0 ≤ cost x ∧ cost x ≤ 1) :
    ∀ n (h : Hist X n), 0 ≤ cumulative (fun _ _ x => cost x) n h ∧
      cumulative (fun _ _ x => cost x) n h ≤ (n:ℝ) := by
  intro n
  induction n with
  | zero => intro h; simp [cumulative]
  | succ n ih =>
    intro h
    have hp := ih h.1
    have hh := hc h.2
    simp only [cumulative,Nat.cast_add,Nat.cast_one]
    constructor <;> linarith

theorem player_nonneg (A : Algorithm I) (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    ∀ n (e : Hist (I → Bool) n) a, 0 ≤ playerWeight (choice A.p q) n e a := by
  intro n
  induction n with
  | zero => intro e a; exact zero_le_one
  | succ n ih =>
    intro e a
    apply mul_nonneg (ih e.1 a.1)
    apply mul_nonneg (A.nonneg _ _ _)
    cases a.2.2 <;> simp only [ErasedBandit.bernoulli] <;> linarith

theorem gap_identity (j : I) : ∀ n (e : Hist (I → Bool) n) a,
    cumulative (fun _ _ x => regretStep j x) n (zip n e a) =
      learnerTotal n (zip n e a)-tableTotal j n e := by
  intro n
  induction n with
  | zero => intro e a; simp [cumulative,learnerTotal,tableTotal]
  | succ n ih =>
    intro e a
    change cumulative (fun _ _ x => regretStep j x) n (zip n e.1 a.1)+
      (loss (e.2 a.2.1)-loss (e.2 j)) =
      (learnerTotal n (zip n e.1 a.1)+loss (e.2 a.2.1))-(tableTotal j n e.1+loss (e.2 j))
    rw [ih]
    ring

theorem fixed_regret_identity (A : Algorithm I) (q : ℝ) (j : I) (N : ℕ) (table : Hist (I → Bool) N) :
    fixedRegret A.p q j N table = fixedLearner A q N table-tableTotal j N table := by
  unfold fixedRegret
  simp_rw [gap_identity]
  change DRGPR.mean (playerWeight (choice A.p q) N table)
    (fun a => learnerTotal N (zip N table a)-tableTotal j N table) = _
  rw [DRGPR.mean_sub,DRGPR.mean_const _ (fixed_player_normalized A.p A.normalized q N table)]
  rfl

theorem best_nonneg [Nonempty I] (N : ℕ) (table : Hist (I → Bool) N) :
    0 ≤ sInf (Set.range (fun j => tableTotal j N table)) := by
  apply le_csInf (Set.range_nonempty _)
  intro x hx
  obtain ⟨j,rfl⟩ := hx
  exact (total_bounds (fun row : I → Bool => loss (row j)) (fun _ => loss_bounds _) N table).1

theorem comparator_dominates (N : ℕ) (table : Hist (I → Bool) N) (j : I) :
    sInf (Set.range (fun i => tableTotal i N table)) ≤ tableTotal j N table := by
  apply csInf_le
  · refine ⟨0,?_⟩
    intro x hx
    obtain ⟨i,rfl⟩ := hx
    exact (total_bounds (fun row : I → Bool => loss (row i)) (fun _ => loss_bounds _) N table).1
  · exact ⟨j,rfl⟩

theorem regret_upper [Nonempty I] (A : Algorithm I) (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (N : ℕ) (table : Hist (I → Bool) N) : regret A q N table ≤ N := by
  have h := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset (Hist (I × Bool) N))) =>
    mul_le_mul_of_nonneg_left
      (total_bounds (fun x : Event I => loss (x.1 x.2.1)) (fun _ => loss_bounds _) N (zip N table a)).2
      (player_nonneg A q hq hq1 N table a))
  rw [← Finset.sum_mul,fixed_player_normalized A.p A.normalized q N table,one_mul] at h
  have hb := best_nonneg N table
  change (∑ a, playerWeight (choice A.p q) N table a * learnerTotal N (zip N table a)) ≤ (N:ℝ) at h
  dsimp [regret,fixedLearner]
  linarith

theorem fixed_table_regret_lower (A : Algorithm I) (q : ℝ) (N : ℕ) (hN : 0 < N) (j₀ : I)
    (hK : (2:ℝ) ≤ Fintype.card I) (hq : 0 < q) (hq1 : q ≤ 1) :
    ∃ table, (1/32:ℝ)*min (N:ℝ) (Real.sqrt ((Fintype.card I)*N/q)) ≤ regret A q N table := by
  obtain ⟨j,table,h⟩ := exists_fixed_hard_table A.p A.nonneg A.normalized q N hN j₀ hK hq hq1
  rw [fixed_regret_identity] at h
  refine ⟨table,?_⟩
  have hc := comparator_dominates N table j
  dsimp [regret]
  linarith

/-- Complete finite oblivious-erasure minimax lower bound, including the
algorithm's observable history, actual task loss, a fixed table, and inf-sup. -/
theorem minimax_lower (q : ℝ) (N : ℕ) (hN : 0 < N) (j₀ : I)
    (hK : (2:ℝ) ≤ Fintype.card I) (hq : 0 < q) (hq1 : q ≤ 1) :
    (1/32:ℝ)*min (N:ℝ) (Real.sqrt ((Fintype.card I)*N/q)) ≤ minimax (I:=I) q N := by
  letI : Nonempty I := ⟨j₀⟩
  letI : Nonempty (Algorithm I) := ⟨constantAlgorithm j₀⟩
  apply le_csInf (Set.range_nonempty _)
  intro x hx
  obtain ⟨A,rfl⟩ := hx
  obtain ⟨table,ht⟩ := fixed_table_regret_lower A q N hN j₀ hK hq hq1
  apply le_trans ht
  apply le_csSup
  · refine ⟨(N:ℝ),?_⟩
    intro y hy
    obtain ⟨e,rfl⟩ := hy
    exact regret_upper A q hq.le hq1 N e
  · exact ⟨table,rfl⟩

end DRGPR.ObliviousMinimax
#print axioms DRGPR.ObliviousMinimax.loss_bounds
#print axioms DRGPR.ObliviousMinimax.total_bounds
#print axioms DRGPR.ObliviousMinimax.player_nonneg
#print axioms DRGPR.ObliviousMinimax.gap_identity
#print axioms DRGPR.ObliviousMinimax.fixed_regret_identity
#print axioms DRGPR.ObliviousMinimax.best_nonneg
#print axioms DRGPR.ObliviousMinimax.comparator_dominates
#print axioms DRGPR.ObliviousMinimax.regret_upper
#print axioms DRGPR.ObliviousMinimax.fixed_table_regret_lower
#print axioms DRGPR.ObliviousMinimax.minimax_lower
