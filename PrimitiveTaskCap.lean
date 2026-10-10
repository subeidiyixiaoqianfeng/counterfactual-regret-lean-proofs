import PrimitiveJointBounds

noncomputable section
open scoped BigOperators
namespace DRGPR.PrimitiveTaskCap
open DependentBlocks GrowingInformation GrowingTableReduction GrowingTaskLower
open MultiphaseOblivious (Table Coins Environment)
variable {K : ℕ → ℕ} {n : ℕ}

theorem task_le_horizon (hn : 0 < n) :
    ∀ m (e : History (fun r => Table (Fin (K r)) n) m)
      (a : History (fun r => Coins (Fin (K r)) n) m), taskCost m e a ≤ (m:ℝ)*n := by
  intro m
  induction m with
  | zero => intro e a; simp [taskCost,played,total]
  | succ m ih =>
    intro e a
    have hi := ih e.1 a.1
    have hb := GrowingPrimitiveUpper.boundary_bound m a.1 a.2
    have hl := (ObliviousMinimax.total_bounds
      (fun z : ObliviousInformation.Event (Fin (K m)) => ObliviousInformation.loss (z.1 z.2.1))
      (fun _ => ObliviousMinimax.loss_bounds _) n (ObliviousFactorization.zip n e.2 a.2)).2
    change ObliviousMinimax.learnerTotal n _ ≤ (n:ℝ) at hl
    have hs : ((WindowLedger.switches (labels m a.2) n).card:ℝ)+1 ≤ (n:ℝ) := by
      have hh := TaskSaturation.internal_switch_count (labels m a.2) n
      exact_mod_cast (show (WindowLedger.switches (labels m a.2) n).card+1 ≤ n by omega)
    rw [GrowingPrimitiveUpper.task_cost_split]
    change taskCost m e.1 a.1+(ObliviousMinimax.learnerTotal n _+
      (WindowLedger.switches (labels m a.2) n).card)/2+boundary m a.1 a.2/2 ≤ _
    push_cast
    linarith

theorem regret_le_horizon (hK : ∀ r, 2 ≤ K r) (A : Master K n) (hn : 0 < n)
    (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (m : ℕ)
    (e : History (fun r => Table (Fin (K r)) n) m) : regret hK A q m e ≤ (m:ℝ)*n := by
  let he := liftTables hK m e
  have hh := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset (History (fun r => Coins (Fin (K r)) n) m))) =>
    mul_le_mul_of_nonneg_left (task_le_horizon hn m (tables m he) a)
      (DependentFactorization.weight_nonneg (response A q) (response_nonneg A q hq hq1) m he a))
  rw [← Finset.sum_mul,DependentFactorization.normalized _ (response_normalized A q),one_mul] at hh
  have hb := best_nonneg hK m e
  change fixedTask A q m he ≤ (m:ℝ)*n at hh
  unfold regret
  linarith

theorem minimax_le_horizon (hK : ∀ r, 2 ≤ K r) (hn : 0 < n)
    (q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1) (m : ℕ) : minimax hK q n m ≤ (m:ℝ)*n := by
  let A := ScheduledPrimitiveMaster.master K n q hK
  have hw : worst hK A q m ≤ (m:ℝ)*n := by
    apply csSup_le
    · exact ⟨regret hK A q m (tables m (defaultEnvironment (n:=n) hK m)),
        ⟨tables m (defaultEnvironment (n:=n) hK m),rfl⟩⟩
    · rintro _ ⟨e,rfl⟩
      exact regret_le_horizon hK A hn q hq.le hq1 m e
  apply le_trans ?_ hw
  apply csInf_le
  · refine ⟨-((m:ℝ)*((n:ℝ)+1)),?_⟩
    rintro _ ⟨A,rfl⟩
    exact PrimitiveJointBounds.worst_lower_bound hK A q hq.le hq1 m
  · exact ⟨A,rfl⟩

/-- The paid growing two-sided theorem on one primitive mathematical model.
The lower side contains the fully proved information term only. -/
theorem paid_two_sided (B m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hB : 4*m ≤ B)
    (q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1) :
    let hK := fun r => PaidSchedule.registered_two B m (r+1) hm hB
    (1/128:ℝ)*min ((m:ℝ)*n) (Real.sqrt ((m:ℝ)*B*((m:ℝ)*n)/q))-(m:ℝ)/2 ≤ minimax hK q n m ∧
    minimax hK q n m ≤ min ((m:ℝ)*n)
      (4*(((m:ℝ)*B*Real.log B)^((1:ℝ)/3)*((m:ℝ)*n)^((2:ℝ)/3)+
        Real.sqrt ((m:ℝ)*B*Real.log B*((m:ℝ)*n)/q))+5*m) := by
  have h := PrimitiveJointBounds.paid_common_model B m n hm hn hB q hq hq1
  exact ⟨h.2.2.2.1,le_min (minimax_le_horizon _ hn q hq hq1 m) h.2.2.2.2⟩

end DRGPR.PrimitiveTaskCap
#print axioms DRGPR.PrimitiveTaskCap.task_le_horizon
#print axioms DRGPR.PrimitiveTaskCap.regret_le_horizon
#print axioms DRGPR.PrimitiveTaskCap.minimax_le_horizon
#print axioms DRGPR.PrimitiveTaskCap.paid_two_sided
