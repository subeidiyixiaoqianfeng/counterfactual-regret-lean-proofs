import DependentBlocks

noncomputable section
open scoped BigOperators
namespace DRGPR.RestartedGrowing
open FiniteController PhaseAlgorithm PhaseSwitching TunedPhase SupportedInformation

/-- Fixed phase tables and the public availability counts. No regret bound,
global sampling law, moment bound, or best comparator is an input field. -/
structure Model where
  n : ℕ
  n_pos : 0 < n
  K : ℕ → ℕ
  K_two : ∀ r, 2 ≤ K r
  q : ℝ
  q_pos : 0 < q
  q_le : q ≤ 1
  loss : (r : ℕ) → Fin (K r) → Fin n → ℝ
  loss_nonneg : ∀ r i t, 0 ≤ loss r i t
  loss_le : ∀ r i t, loss r i t ≤ 1

namespace Model
variable (M : Model)

def fallback (r : ℕ) : Fin (M.K r) := ⟨0,by have := M.K_two r; omega⟩
def b (r : ℕ) : ℕ := runCap M.n (M.K r)
def V (r : ℕ) : ℝ := varianceBudget M.n (M.b r) (M.K r) M.q
def η (r : ℕ) : ℝ := rate (Real.log (M.K r)) (M.V r)

theorem K_pos (r : ℕ) : (0:ℝ) < M.K r := by have := M.K_two r; exact_mod_cast (by omega : 0 < M.K r)
theorem log_pos (r : ℕ) : 0 < Real.log (M.K r) :=
  Real.log_pos (by have := M.K_two r; exact_mod_cast (by omega : 1 < M.K r))
theorem eta_pos (r : ℕ) : 0 < M.η r :=
  rate_pos _ _ (M.log_pos r) (varianceBudget_pos M.n (M.b r) (M.K r) M.q M.n_pos (M.K_pos r) M.q_pos)

def phase (r : ℕ) : Program (Fin (M.K r)) (Fin M.n → Bool) :=
  algorithm M.n (M.b r) M.q (M.η r) M.q_pos M.q_le (M.eta_pos r)
    (by simpa using M.K_pos r) (M.loss r) (M.loss_nonneg r) (M.loss_le r)

abbrev Record (r : ℕ) := Hist (Fin (M.K r) × (Fin M.n → Bool)) M.n
abbrev Past (r : ℕ) := DependentBlocks.History M.Record r

def kernel (r : ℕ) (_h : M.Past r) (a : M.Record r) : ℝ := pathLaw (M.phase r).kernel M.n a

theorem kernel_normalized (r : ℕ) (h : M.Past r) : ∑ a, M.kernel r h a=1 :=
  (M.phase r).law_normalized M.n
theorem kernel_nonneg (r : ℕ) (h : M.Past r) (a : M.Record r) : 0 ≤ M.kernel r h a :=
  (M.phase r).law_nonneg M.n a

def phaseCost (r : ℕ) (a : M.Record r) : ℝ :=
  taskTotal M.n (M.b r) (M.loss r) a (M.fallback r)
def baseComparator (r : ℕ) (j : Fin (M.K r)) : ℝ := comparatorTotal M.n (M.loss r) j/2
def upper (r : ℕ) : ℝ :=
  4*(((M.K r:ℝ)*Real.log (M.K r))^((1:ℝ)/3)*(M.n:ℝ)^((2:ℝ)/3)+
    Real.sqrt ((M.K r:ℝ)*Real.log (M.K r)*M.n/M.q)+1)

theorem phase_upper (r : ℕ) (j : Fin (M.K r)) :
    (∑ a, pathLaw (M.phase r).kernel M.n a*M.phaseCost r a)-M.baseComparator r j ≤ M.upper r := by
  have hk : (2:ℝ) ≤ Fintype.card (Fin (M.K r)) := by simpa using (show (2:ℝ) ≤ M.K r by exact_mod_cast M.K_two r)
  have h := actual_tuned_phase M.n M.n_pos M.q M.q_pos M.q_le hk
    (M.loss r) (M.loss_nonneg r) (M.loss_le r) (M.fallback r) j
  simpa only [Fintype.card_fin,phaseCost,baseComparator,upper,phase,b,η,V] using h

def label (r : ℕ) (a : M.Record r) (t : ℕ) : ℕ :=
  (played M.n (M.b r) a (M.fallback r) t).val

/-- This is the actual cross-phase switch. The two phase arm types may differ. -/
def boundary : (r : ℕ) → M.Past r → M.Record r → ℝ
  | 0, _, _ => 0
  | r+1, h, a => if M.label r h.2 (M.n-1)=M.label (r+1) a 0 then 0 else 1

theorem boundary_bounds (r : ℕ) (h : M.Past r) (a : M.Record r) :
    0 ≤ M.boundary r h a ∧ M.boundary r h a ≤ 1 := by
  cases r with
  | zero => simp [boundary]
  | succ r =>
    change 0 ≤ (if M.label r h.2 (M.n-1)=M.label (r+1) a 0 then (0:ℝ) else 1) ∧
      (if M.label r h.2 (M.n-1)=M.label (r+1) a 0 then (0:ℝ) else 1) ≤ 1
    split_ifs <;> norm_num

def stage (r : ℕ) (h : M.Past r) (a : M.Record r) : ℝ := M.phaseCost r a+M.boundary r h a/2

theorem conditional_stage_upper (r : ℕ) (h : M.Past r) (j : Fin (M.K r)) :
    (∑ a, M.kernel r h a*(M.stage r h a-M.baseComparator r j)) ≤ M.upper r+1/2 := by
  have hb : (∑ a, M.kernel r h a*(M.boundary r h a/2)) ≤ (1/2:ℝ) := by
    calc
      _ ≤ ∑ a, M.kernel r h a*(1/2:ℝ) := Finset.sum_le_sum (fun a _ =>
        mul_le_mul_of_nonneg_left (by linarith [(M.boundary_bounds r h a).2]) (M.kernel_nonneg r h a))
      _ = _ := by rw [← Finset.sum_mul,M.kernel_normalized,one_mul]
  have hp := M.phase_upper r j
  simp only [stage,mul_sub,mul_add,Finset.sum_sub_distrib,Finset.sum_add_distrib,
    ← Finset.sum_mul,M.kernel_normalized,one_mul]
  change (∑ a, M.kernel r h a*M.phaseCost r a)-M.baseComparator r j ≤ M.upper r at hp
  linarith

def learnerCost (m : ℕ) : ℝ :=
  ∑ h, DependentBlocks.law M.kernel m h*DependentBlocks.total M.stage m h

def comparatorSwitch (v : (r : ℕ) → Fin (M.K r)) : ℕ → ℝ
  | 0 => 0
  | r+1 => if (v r).val=(v (r+1)).val then 0 else 1

def comparatorCost (v : (r : ℕ) → Fin (M.K r)) (m : ℕ) : ℝ :=
  ∑ r ∈ Finset.range m, (M.baseComparator r (v r)+M.comparatorSwitch v r/2)

theorem comparator_base_le (v : (r : ℕ) → Fin (M.K r)) (m : ℕ) :
    (∑ r ∈ Finset.range m, M.baseComparator r (v r)) ≤ M.comparatorCost v m := by
  apply Finset.sum_le_sum
  intro r _
  have hs : 0 ≤ M.comparatorSwitch v r := by
    cases r with
    | zero => exact le_rfl
    | succ r =>
      change 0 ≤ (if (v r).val=(v (r+1)).val then (0:ℝ) else 1)
      split_ifs <;> norm_num
  linarith

/-- The total bound is obtained from the actual recursive phase kernels.
The comparator is fixed outside expectation and pays its own phase switches. -/
theorem expected_regret (v : (r : ℕ) → Fin (M.K r)) (m : ℕ) :
    M.learnerCost m-M.comparatorCost v m ≤ ∑ r ∈ Finset.range m, (M.upper r+1/2) := by
  have h := DependentBlocks.expected_total_le M.kernel
    (fun r hist a => M.stage r hist a-M.baseComparator r (v r))
    M.kernel_nonneg M.kernel_normalized (fun r => M.upper r+1/2)
    (fun r hist => M.conditional_stage_upper r hist (v r)) m
  simp_rw [DependentBlocks.subtract_deterministic] at h
  simp only [mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul,
    DependentBlocks.normalized M.kernel M.kernel_normalized,one_mul] at h
  have hc := M.comparator_base_le v m
  change M.learnerCost m-_ ≤ _ at h
  linarith

theorem counterfactual_infimum (m : ℕ) :
    M.learnerCost m-sInf (Set.range (fun v : (r : ℕ) → Fin (M.K r) => M.comparatorCost v m)) ≤
      ∑ r ∈ Finset.range m, (M.upper r+1/2) := by
  apply DRGPR.infimum_transfer
  · exact ⟨M.comparatorCost M.fallback m,⟨M.fallback,rfl⟩⟩
  · intro x hx
    obtain ⟨v,rfl⟩ := hx
    exact M.expected_regret v m

end Model
end DRGPR.RestartedGrowing
#print axioms DRGPR.RestartedGrowing.Model.K_pos
#print axioms DRGPR.RestartedGrowing.Model.log_pos
#print axioms DRGPR.RestartedGrowing.Model.eta_pos
#print axioms DRGPR.RestartedGrowing.Model.kernel_normalized
#print axioms DRGPR.RestartedGrowing.Model.kernel_nonneg
#print axioms DRGPR.RestartedGrowing.Model.phase_upper
#print axioms DRGPR.RestartedGrowing.Model.boundary_bounds
#print axioms DRGPR.RestartedGrowing.Model.conditional_stage_upper
#print axioms DRGPR.RestartedGrowing.Model.comparator_base_le
#print axioms DRGPR.RestartedGrowing.Model.expected_regret
#print axioms DRGPR.RestartedGrowing.Model.counterfactual_infimum
