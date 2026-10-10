import VariableRunController

noncomputable section
open scoped BigOperators
namespace DRGPR.PhaseSchedule
open SupportedInformation

/-- Actual primitive slots in the r-th deterministic capped run. -/
def slots (T b r : ℕ) : Finset (Fin T) := Finset.univ.filter (fun t => t.val/b=r)

theorem mem_slots (T b r : ℕ) (t : Fin T) : t ∈ slots T b r ↔ t.val/b=r := by
  simp [slots]

theorem slots_card_le (T b r : ℕ) (hb : 0 < b) : (slots T b r).card ≤ b := by
  have h := Finset.card_le_card_of_injOn (fun t : Fin T => t.val%b)
    (s := slots T b r) (t := Finset.range b)
    (fun t _ => Finset.mem_range.mpr (Nat.mod_lt t.val hb)) (by
      intro t ht u hu he
      have ht' := (mem_slots T b r t).mp ht
      have hu' := (mem_slots T b r u).mp hu
      have htm := Nat.mod_add_div t.val b
      have hum := Nat.mod_add_div u.val b
      rw [ht'] at htm
      rw [hu'] at hum
      dsimp only at he
      apply Fin.ext
      omega)
  simpa using h

theorem slot_unique (T b : ℕ) (t : Fin T) :
    ∃! r, r < T ∧ t ∈ slots T b r := by
  refine ⟨t.val/b,⟨lt_of_le_of_lt (Nat.div_le_self _ _) t.isLt,(mem_slots _ _ _ _).mpr rfl⟩,?_⟩
  intro r hr
  exact ((mem_slots _ _ _ _).mp hr.2).symm

theorem partition_sum (T b : ℕ) (f : Fin T → ℝ) :
    (∑ r ∈ Finset.range T, ∑ t ∈ slots T b r, f t)=∑ t, f t := by
  simp only [slots,Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  have ht : t.val/b < T := lt_of_le_of_lt (Nat.div_le_self _ _) t.isLt
  simp [eq_comm,ht]

theorem total_duration (T b : ℕ) :
    (∑ r ∈ Finset.range T, ((slots T b r).card:ℝ))=(T:ℝ) := by
  have h := partition_sum T b (fun _ => (1:ℝ))
  simpa using h

theorem empty_after (T b r : ℕ) (hb : 0 < b) (hr : T ≤ r*b) : slots T b r=∅ := by
  apply Finset.eq_empty_iff_forall_not_mem.mpr
  intro t ht
  have he := (mem_slots _ _ _ _).mp ht
  have hd := Nat.div_mul_le_self t.val b
  rw [he] at hd
  omega

theorem duration_path {I : Type} (T b : ℕ) :
    ∀ n (h : Hist (I × (Fin T → Bool)) n),
      cumulative (VariableRunController.duration (fun r _ => slots T b r)) n h=
        ∑ r ∈ Finset.range n, ((slots T b r).card:ℝ) := by
  intro n
  induction n with
  | zero => intro h; simp [cumulative]
  | succ n ih =>
    intro h
    change cumulative (VariableRunController.duration (fun r _ => slots T b r)) n h.1+
      ((slots T b n).card:ℝ)=_
    rw [ih,Finset.sum_range_succ]

theorem path_duration_exact {I : Type} (T b : ℕ)
    (h : Hist (I × (Fin T → Bool)) T) :
    cumulative (VariableRunController.duration (fun r _ => slots T b r)) T h=(T:ℝ) := by
  rw [duration_path,total_duration]

end DRGPR.PhaseSchedule
#print axioms DRGPR.PhaseSchedule.mem_slots
#print axioms DRGPR.PhaseSchedule.slots_card_le
#print axioms DRGPR.PhaseSchedule.slot_unique
#print axioms DRGPR.PhaseSchedule.partition_sum
#print axioms DRGPR.PhaseSchedule.total_duration
#print axioms DRGPR.PhaseSchedule.empty_after
#print axioms DRGPR.PhaseSchedule.duration_path
#print axioms DRGPR.PhaseSchedule.path_duration_exact
