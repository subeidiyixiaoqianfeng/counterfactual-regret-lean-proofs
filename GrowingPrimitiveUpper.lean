import PrimitiveTunedPhase
import ScheduledPrimitiveMaster

noncomputable section
open scoped BigOperators
namespace DRGPR.GrowingPrimitiveUpper
open DependentBlocks GrowingInformation GrowingTableReduction GrowingTaskLower
open MultiphaseOblivious (Table Coins Transcript Environment)
variable {K : ℕ → ℕ} {n : ℕ}

def phaseUpper (K : ℕ → ℕ) (n : ℕ) (q : ℝ) (r : ℕ) : ℝ :=
  4*(((K r:ℝ)*Real.log (K r))^((1:ℝ)/3)*(n:ℝ)^((2:ℝ)/3)+
    Real.sqrt ((K r:ℝ)*Real.log (K r)*n/q)+1)

theorem boundary_bound (r : ℕ) (a : History (fun s => Coins (Fin (K s)) n) r)
    (c : Coins (Fin (K r)) n) : boundary r a c ≤ 1 := by
  cases r with
  | zero => norm_num [boundary]
  | succ r =>
    change (if labels r a.2 (n-1)=labels (r+1) c 0 then (0:ℝ) else 1) ≤ 1
    split_ifs <;> norm_num

theorem task_cost_split (r : ℕ) (e : History (fun s => Table (Fin (K s)) n) (r+1))
    (a : History (fun s => Coins (Fin (K s)) n) (r+1)) :
    taskCost (r+1) e a=taskCost r e.1 a.1+
      PrimitiveTaskRegret.taskTotal Fin.val n e.2 a.2+boundary r a.1 a.2/2 := by
  change ((played r e.1 a.1+ObliviousMinimax.learnerTotal n (ObliviousFactorization.zip n e.2 a.2))+
    (total switchStep r a.1+((WindowLedger.switches (labels r a.2) n).card+boundary r a.1 a.2)))/2=
    (played r e.1 a.1+total switchStep r a.1)/2+
    (ObliviousMinimax.learnerTotal n (ObliviousFactorization.zip n e.2 a.2)+
      (WindowLedger.switches (labels r a.2) n).card)/2+boundary r a.1 a.2/2
  ring

theorem concrete_phase_upper (hK : ∀ r, 2 ≤ K r) (hn : 0 < n)
    (q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1) (r : ℕ)
    (h : History (fun s => Transcript (Fin (K s)) n) r) (e : Table (Fin (K r)) n) (j : Fin (K r)) :
    (∑ a, ObliviousFactorization.playerWeight
      (ObliviousInformation.choice ((ScheduledPrimitiveMaster.master K n q hK).policy r h).p q) n e a *
      PrimitiveTaskRegret.taskTotal Fin.val n e a)-ObliviousMinimax.tableTotal j n e/2 ≤
      phaseUpper K n q r := by
  have hk : (2:ℝ) ≤ Fintype.card (Fin (K r)) := by simpa using (show (2:ℝ) ≤ K r by exact_mod_cast hK r)
  have ht := PrimitiveTunedPhase.tuned_primitive_phase Fin.val n hn e q hq hq1 hk
    (⟨0,by have := hK r; omega⟩ : Fin (K r)) j
  simpa only [ScheduledPrimitiveMaster.master,phaseUpper,Fintype.card_fin] using ht

/-- Composition over actual primitive histories. This lemma makes the
conditional phase premise explicit, and the next theorem discharges it
using the public, non-oracle primitive algorithm above. -/
theorem compose_phase_upper (A : Master K n) (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (U : ℕ → ℝ)
    (hU : ∀ r (h : History (fun s => Transcript (Fin (K s)) n) r)
      (e : Table (Fin (K r)) n) (j : Fin (K r)),
      (∑ a, ObliviousFactorization.playerWeight (ObliviousInformation.choice (A.policy r h).p q) n e a *
        PrimitiveTaskRegret.taskTotal Fin.val n e a)-ObliviousMinimax.tableTotal j n e/2 ≤ U r) :
    ∀ m (e : History (fun r => Environment (Fin (K r)) n) m)
      (v : History (fun r => Fin (K r)) m),
    fixedTask A q m e-comparatorCost m (tables m e) v ≤ ∑ r ∈ Finset.range m, (U r+1/2) := by
  intro m
  induction m with
  | zero => intro e v; simp [fixedTask,History,DependentFactorization.weight,taskCost,played,total,comparatorCost]
  | succ m ih =>
    intro e v
    let w := DependentFactorization.weight (response A q) m e.1
    let c := ObliviousMinimax.tableTotal v.2 n e.2.2/2
    have hc (a : History (fun r => Coins (Fin (K r)) n) m) :
        (∑ x, response A q m e.1 a e.2 x *
          (PrimitiveTaskRegret.taskTotal Fin.val n e.2.2 x+boundary m a x/2)) ≤ c+U m+1/2 := by
      have hp := hU m (DependentFactorization.project visible m (DependentFactorization.zip m e.1 a)) e.2.2 v.2
      change (∑ x, response A q m e.1 a e.2 x * PrimitiveTaskRegret.taskTotal Fin.val n e.2.2 x)-c ≤ U m at hp
      have hs := Finset.sum_le_sum (fun x (_ : x ∈ (Finset.univ : Finset (Coins (Fin (K m)) n))) =>
        mul_le_mul_of_nonneg_left (show boundary m a x/2 ≤ (1/2:ℝ) by linarith [boundary_bound m a x])
          (response_nonneg A q hq hq1 m e.1 a e.2 x))
      rw [← Finset.sum_mul,response_normalized,one_mul] at hs
      simp only [mul_add,Finset.sum_add_distrib]
      linarith
    have hstep : fixedTask A q (m+1) e ≤ fixedTask A q m e.1+c+U m+1/2 := by
      unfold fixedTask
      change (∑ a : History (fun r => Coins (Fin (K r)) n) m × Coins (Fin (K m)) n,
        (w a.1*response A q m e.1 a.1 e.2 a.2)*taskCost (m+1) (tables (m+1) e) a) ≤ _
      rw [Fintype.sum_prod_type]
      simp_rw [task_cost_split]
      have hh := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset (History (fun r => Coins (Fin (K r)) n) m))) =>
        mul_le_mul_of_nonneg_left (hc a)
          (DependentFactorization.weight_nonneg (response A q) (response_nonneg A q hq hq1) m e.1 a))
      have hnw : ∑ a, w a=1 := DependentFactorization.normalized _ (response_normalized A q) m e.1
      have heq (a : History (fun r => Coins (Fin (K r)) n) m) :
          (∑ x, (w a*response A q m e.1 a e.2 x)*
            (taskCost m (tables m e.1) a+PrimitiveTaskRegret.taskTotal Fin.val n e.2.2 x+boundary m a x/2))=
          w a*taskCost m (tables m e.1) a+w a*(∑ x, response A q m e.1 a e.2 x*
            (PrimitiveTaskRegret.taskTotal Fin.val n e.2.2 x+boundary m a x/2)) := by
        simp only [mul_add,Finset.sum_add_distrib,Finset.mul_sum,mul_assoc]
        have hfirst : (∑ x, w a*(response A q m e.1 a e.2 x*taskCost m (tables m e.1) a))=
            w a*taskCost m (tables m e.1) a := by
          rw [← Finset.mul_sum,← Finset.sum_mul,response_normalized,one_mul]
        rw [hfirst]
        ring
      change (∑ a, ∑ x, (w a*response A q m e.1 a e.2 x)*
        (taskCost m (tables m e.1) a+PrimitiveTaskRegret.taskTotal Fin.val n e.2.2 x+boundary m a x/2)) ≤ _
      simp_rw [heq]
      rw [Finset.sum_add_distrib]
      change (∑ a, w a*_)+_ ≤ (∑ a, w a*_)+c+U m+1/2
      change (∑ a, w a*_ ) ≤ ∑ a, w a*(c+U m+1/2) at hh
      rw [← Finset.sum_mul,hnw,one_mul] at hh
      linarith
    have hi := ih e.1 v.1
    have hs := (comparator_switch_bounds m v.1 v.2).1
    change fixedTask A q (m+1) e-(comparatorCost m (tables m e.1) v.1+
      (ObliviousMinimax.tableTotal v.2 n e.2.2+comparatorSwitch m v.1 v.2)/2) ≤ _
    rw [Finset.sum_range_succ]
    dsimp only [c] at hstep
    linarith

/-- The growing primitive learner competes with exactly the finite comparator
path class used by the information lower theorem, on its own execution law. -/
theorem growing_primitive_regret (hK : ∀ r, 2 ≤ K r) (hn : 0 < n)
    (q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1) (m : ℕ)
    (e : History (fun r => Table (Fin (K r)) n) m) :
    regret hK (ScheduledPrimitiveMaster.master K n q hK) q m e ≤
      ∑ r ∈ Finset.range m, (phaseUpper K n q r+1/2) := by
  have h := compose_phase_upper (ScheduledPrimitiveMaster.master K n q hK) q hq.le hq1
    (phaseUpper K n q) (concrete_phase_upper hK hn q hq hq1) m (liftTables hK m e)
  rw [tables_lift] at h
  unfold regret best
  apply DRGPR.infimum_transfer
  · exact ⟨comparatorCost m e (targetPath m (defaultEnvironment (n:=n) hK m)),
      ⟨targetPath m (defaultEnvironment (n:=n) hK m),rfl⟩⟩
  · rintro _ ⟨v,rfl⟩
    exact h v

end DRGPR.GrowingPrimitiveUpper
#print axioms DRGPR.GrowingPrimitiveUpper.boundary_bound
#print axioms DRGPR.GrowingPrimitiveUpper.task_cost_split
#print axioms DRGPR.GrowingPrimitiveUpper.concrete_phase_upper
#print axioms DRGPR.GrowingPrimitiveUpper.compose_phase_upper
#print axioms DRGPR.GrowingPrimitiveUpper.growing_primitive_regret
