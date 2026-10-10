import GrowingPrimitiveUpper
import PaidInformationLower

noncomputable section
open scoped BigOperators
namespace DRGPR.PrimitiveJointBounds
open DependentBlocks GrowingInformation GrowingTableReduction GrowingTaskLower GrowingPrimitiveUpper
open MultiphaseOblivious (Table Coins Environment)
variable {K : ℕ → ℕ} {n : ℕ}

theorem comparator_upper : ∀ m (e : History (fun r => Table (Fin (K r)) n) m)
    (v : History (fun r => Fin (K r)) m), comparatorCost m e v ≤ (m:ℝ)*((n:ℝ)+1) := by
  intro m
  induction m with
  | zero => intro e v; simp [comparatorCost]
  | succ m ih =>
    intro e v
    have hi := ih e.1 v.1
    have hl := (ObliviousMinimax.total_bounds
      (fun row : Fin (K m) → Bool => ObliviousInformation.loss (row v.2))
      (fun _ => ObliviousMinimax.loss_bounds _) n e.2).2
    change ObliviousMinimax.tableTotal v.2 n e.2 ≤ (n:ℝ) at hl
    have hs := (comparator_switch_bounds m v.1 v.2).2
    change comparatorCost m e.1 v.1+_/2 ≤ _
    push_cast
    have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg n
    linarith

theorem fixed_task_nonneg (A : Master K n) (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (m : ℕ) (e : History (fun r => Environment (Fin (K r)) n) m) : 0 ≤ fixedTask A q m e := by
  apply Finset.sum_nonneg
  intro a _
  apply mul_nonneg (DependentFactorization.weight_nonneg (response A q) (response_nonneg A q hq hq1) m e a)
  have ht := (task_bounds m (tables m e) a).1
  have hp := (played_bounds m (tables m e) a).1
  linarith

theorem regret_lower_bound (hK : ∀ r, 2 ≤ K r) (A : Master K n)
    (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (m : ℕ)
    (e : History (fun r => Table (Fin (K r)) n) m) :
    -((m:ℝ)*((n:ℝ)+1)) ≤ regret hK A q m e := by
  let v := targetPath m (defaultEnvironment (n:=n) hK m)
  have hb := (best_le m e v).trans (comparator_upper m e v)
  have hc := fixed_task_nonneg A q hq hq1 m (liftTables hK m e)
  unfold regret
  linarith

theorem worst_lower_bound (hK : ∀ r, 2 ≤ K r) (A : Master K n)
    (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (m : ℕ) :
    -((m:ℝ)*((n:ℝ)+1)) ≤ worst hK A q m := by
  let e := tables m (defaultEnvironment (n:=n) hK m)
  apply (regret_lower_bound hK A q hq hq1 m e).trans
  apply le_csSup
  · refine ⟨(m:ℝ)*((n:ℝ)+1),?_⟩
    rintro _ ⟨e,rfl⟩
    exact regret_upper hK A q hq hq1 m e
  · exact ⟨e,rfl⟩

theorem minimax_upper (hK : ∀ r, 2 ≤ K r) (hn : 0 < n)
    (q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1) (m : ℕ) :
    minimax hK q n m ≤ ∑ r ∈ Finset.range m, (phaseUpper K n q r+1/2) := by
  let A := ScheduledPrimitiveMaster.master K n q hK
  have hw : worst hK A q m ≤ ∑ r ∈ Finset.range m, (phaseUpper K n q r+1/2) := by
    apply csSup_le
    · exact ⟨regret hK A q m (tables m (defaultEnvironment (n:=n) hK m)),
        ⟨tables m (defaultEnvironment (n:=n) hK m),rfl⟩⟩
    · rintro _ ⟨e,rfl⟩
      exact growing_primitive_regret hK hn q hq hq1 m e
  apply le_trans ?_ hw
  apply csInf_le
  · refine ⟨-((m:ℝ)*((n:ℝ)+1)),?_⟩
    rintro _ ⟨A,rfl⟩
    exact worst_lower_bound hK A q hq.le hq1 m
  · exact ⟨A,rfl⟩

/-- Both sides now quantify over the same primitive, causal Master type,
the same erasure law, task loss and finite comparator paths. The lower
side is the information lower bound, not the multiscale switching bound. -/
theorem common_model_bounds (hK : ∀ r, 2 ≤ K r) (hn : 0 < n)
    (q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1) (m : ℕ) :
    (∑ r ∈ Finset.range m, lower K n q r)/2-(m:ℝ)/2 ≤ minimax hK q n m ∧
    minimax hK q n m ≤ ∑ r ∈ Finset.range m, (phaseUpper K n q r+1/2) :=
  ⟨GrowingTaskLower.minimax_lower q n m hn hK hq hq1,minimax_upper hK hn q hq hq1 m⟩

theorem phase_upper_uniform (hK : ∀ r, 2 ≤ K r) (hn : 0 < n)
    (q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1) (B : ℝ) (r : ℕ) (hB : (K r:ℝ) ≤ B) :
    phaseUpper K n q r ≤ 4*((B*Real.log B)^((1:ℝ)/3)*(n:ℝ)^((2:ℝ)/3)+
      Real.sqrt (B*Real.log B*n/q)+1) := by
  let M : RestartedGrowing.Model := ⟨n,hn,K,hK,q,hq,hq1,fun _ _ _ => 0,
    fun _ _ _ => le_rfl,fun _ _ _ => zero_le_one⟩
  exact GrowingRate.phase_bound_uniform M B r hB

theorem uniform_minimax_upper (hK : ∀ r, 2 ≤ K r) (hn : 0 < n)
    (q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1) (m : ℕ) (hm : 0 < m)
    (B : ℝ) (hB : ∀ r < m, (K r:ℝ) ≤ B) :
    minimax hK q n m ≤ 4*(((m:ℝ)*B*Real.log B)^((1:ℝ)/3)*((m:ℝ)*n)^((2:ℝ)/3)+
      Real.sqrt ((m:ℝ)*B*Real.log B*((m:ℝ)*n)/q))+5*m := by
  have hB1 : 1 ≤ B := by
    have hk : (2:ℝ) ≤ K 0 := by exact_mod_cast hK 0
    have hb := hB 0 hm
    linarith
  have ha0 : 0 ≤ B*Real.log B := mul_nonneg (by linarith) (Real.log_nonneg hB1)
  have hmR : (0:ℝ) < m := Nat.cast_pos.mpr hm
  have hs := Finset.sum_le_sum (fun r (hr : r ∈ Finset.range m) =>
    add_le_add_right (phase_upper_uniform hK hn q hq hq1 B r (hB r (Finset.mem_range.mp hr))) (1/2:ℝ))
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul] at hs
  have h := (minimax_upper hK hn q hq hq1 m).trans hs
  have hc := GrowingRate.cube_scaling (m:ℝ) (n:ℝ) (B*Real.log B) hmR (Nat.cast_nonneg _) ha0
  have hsq := GrowingRate.sqrt_scaling (m:ℝ) (n:ℝ) (B*Real.log B) q hmR.le (Nat.cast_nonneg _) ha0 hq
  simp only [← mul_assoc] at hc hsq ⊢
  nlinarith

/-- Paid, strictly growing libraries and the common primitive minimax bounds
are established together. Every prefix of sequential registrations fits B.
No phase regret or hidden optimal schedule is supplied as an assumption. -/
theorem paid_common_model (B m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hB : 4*m ≤ B)
    (q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1) :
    let hK := fun r => PaidSchedule.registered_two B m (r+1) hm hB
    (PaidSchedule.core B+(∑ r ∈ Finset.range m, (PaidSchedule.births B m r).card)=B) ∧
    (∀ r < m, PaidSchedule.registered B m r < PaidSchedule.registered B m (r+1)) ∧
    (∀ r k, k ≤ (PaidSchedule.births B m r).card → PaidSchedule.registered B m r+k ≤ B) ∧
    ((1/128:ℝ)*min ((m:ℝ)*n) (Real.sqrt ((m:ℝ)*B*((m:ℝ)*n)/q))-(m:ℝ)/2 ≤ minimax hK q n m) ∧
    (minimax hK q n m ≤ 4*(((m:ℝ)*B*Real.log B)^((1:ℝ)/3)*((m:ℝ)*n)^((2:ℝ)/3)+
      Real.sqrt ((m:ℝ)*B*Real.log B*((m:ℝ)*n)/q))+5*m) := by
  dsimp only
  refine ⟨PaidSchedule.total_hard_cost B m hm,
    fun r hr => PaidSchedule.strict_birth B m r hm hB hr,?_,
    PaidInformationLower.paid_minimax_lower B m n hm hn hB q hq hq1,?_⟩
  · intro r k hk
    exact (PaidSchedule.every_registration_prefix B m r k hk).trans (PaidSchedule.bounded_registered B m (r+1) hm)
  · exact uniform_minimax_upper (fun r => PaidSchedule.registered_two B m (r+1) hm hB)
      hn q hq hq1 m hm B (fun r _ => Nat.cast_le.mpr (PaidSchedule.bounded_registered B m (r+1) hm))

end DRGPR.PrimitiveJointBounds
#print axioms DRGPR.PrimitiveJointBounds.comparator_upper
#print axioms DRGPR.PrimitiveJointBounds.fixed_task_nonneg
#print axioms DRGPR.PrimitiveJointBounds.regret_lower_bound
#print axioms DRGPR.PrimitiveJointBounds.worst_lower_bound
#print axioms DRGPR.PrimitiveJointBounds.minimax_upper
#print axioms DRGPR.PrimitiveJointBounds.common_model_bounds
#print axioms DRGPR.PrimitiveJointBounds.phase_upper_uniform
#print axioms DRGPR.PrimitiveJointBounds.uniform_minimax_upper
#print axioms DRGPR.PrimitiveJointBounds.paid_common_model
