import RestartedGrowing
import Mathlib.Order.Interval.Finset.Nat

noncomputable section
open scoped BigOperators
namespace DRGPR.PaidSchedule

def core (B : ℕ) : ℕ := B-B/2
def registered (B m r : ℕ) : ℕ := core B+(min r m)*(B/2)/m
def births (B m r : ℕ) : Finset ℕ := Finset.Ico (registered B m r) (registered B m (r+1))

theorem core_is_integer_ceiling (B : ℕ) : core B=(B+1)/2 := by unfold core; omega

theorem initial_count (B m : ℕ) : registered B m 0=core B := by simp [registered]

theorem monotone_registered (B m : ℕ) : Monotone (registered B m) := by
  intro r s hrs
  unfold registered
  exact Nat.add_le_add_left (Nat.div_le_div_right
    (Nat.mul_le_mul_right (B/2) (min_le_min_right m hrs))) _

theorem final_count (B m : ℕ) (hm : 0 < m) : registered B m m=B := by
  simp only [registered,min_self,Nat.mul_div_cancel_left (B/2) hm]
  unfold core
  omega

theorem bounded_registered (B m r : ℕ) (hm : 0 < m) : registered B m r ≤ B := by
  have h := Nat.div_le_div_right (c := m) (Nat.mul_le_mul_right (B/2) (min_le_right r m))
  have h' : min r m*(B/2)/m ≤ B/2 := by simpa [Nat.mul_div_cancel_left (B/2) hm] using h
  unfold registered core
  omega

theorem registered_two (B m r : ℕ) (hm : 0 < m) (hB : 4*m ≤ B) : 2 ≤ registered B m r := by
  have hc : 2 ≤ core B := by rw [core_is_integer_ceiling]; omega
  unfold registered
  exact hc.trans (Nat.le_add_right _ _)

theorem strict_birth (B m r : ℕ) (hm : 0 < m) (hB : 4*m ≤ B) (hr : r < m) :
    registered B m r < registered B m (r+1) := by
  have hi : m ≤ B/2 := by omega
  have hp : r*(B/2)+m ≤ (r+1)*(B/2) := by nlinarith
  have hd := Nat.div_le_div_right (c := m) hp
  rw [Nat.add_div_right _ hm] at hd
  simp only [registered,min_eq_left hr.le,min_eq_left (show r+1 ≤ m by omega)]
  omega

theorem registered_union_births (B m r : ℕ) :
    Finset.range (registered B m r) ∪ births B m r=Finset.range (registered B m (r+1)) := by
  have hm := monotone_registered B m (Nat.le_succ r)
  change registered B m r ≤ registered B m (r+1) at hm
  ext i
  simp only [Finset.mem_union,Finset.mem_range,births,Finset.mem_Ico]
  omega

theorem paid_prefix (B m : ℕ) : ∀ r,
    core B+(∑ s ∈ Finset.range r, (births B m s).card)=registered B m r := by
  intro r
  induction r with
  | zero => simp [initial_count]
  | succ r ih =>
    have hm := monotone_registered B m (Nat.le_succ r)
    change registered B m r ≤ registered B m (r+1) at hm
    rw [Finset.sum_range_succ]
    simp only [births,Nat.card_Ico] at *
    omega

theorem every_registration_prefix (B m r k : ℕ) (hk : k ≤ (births B m r).card) :
    registered B m r+k ≤ registered B m (r+1) := by
  have hm := monotone_registered B m (Nat.le_succ r)
  change registered B m r ≤ registered B m (r+1) at hm
  simp only [births,Nat.card_Ico] at hk
  omega

theorem total_hard_cost (B m : ℕ) (hm : 0 < m) :
    core B+(∑ r ∈ Finset.range m, (births B m r).card)=B := by
  rw [paid_prefix,final_count B m hm]

/-- Instantiate the paper schedule with arbitrary bounded fixed phase tables. -/
def model (B m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hB : 4*m ≤ B)
    (q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1)
    (l : (r : ℕ) → Fin (registered B m (r+1)) → Fin n → ℝ)
    (hl : ∀ r i t, 0 ≤ l r i t) (hl1 : ∀ r i t, l r i t ≤ 1) : RestartedGrowing.Model where
  n := n
  n_pos := hn
  K r := registered B m (r+1)
  K_two r := registered_two B m (r+1) hm hB
  q := q
  q_pos := hq
  q_le := hq1
  loss := l
  loss_nonneg := hl
  loss_le := hl1

theorem paid_growing_regret (B m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hB : 4*m ≤ B)
    (q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1)
    (l : (r : ℕ) → Fin (registered B m (r+1)) → Fin n → ℝ)
    (hl : ∀ r i t, 0 ≤ l r i t) (hl1 : ∀ r i t, l r i t ≤ 1) :
    let M := model B m n hm hn hB q hq hq1 l hl hl1
    M.learnerCost m-sInf (Set.range (fun v : (r : ℕ) → Fin (M.K r) => M.comparatorCost v m)) ≤
      ∑ r ∈ Finset.range m, (M.upper r+1/2) := by
  exact (model B m n hm hn hB q hq hq1 l hl hl1).counterfactual_infimum m

end DRGPR.PaidSchedule
#print axioms DRGPR.PaidSchedule.core_is_integer_ceiling
#print axioms DRGPR.PaidSchedule.initial_count
#print axioms DRGPR.PaidSchedule.monotone_registered
#print axioms DRGPR.PaidSchedule.final_count
#print axioms DRGPR.PaidSchedule.bounded_registered
#print axioms DRGPR.PaidSchedule.registered_two
#print axioms DRGPR.PaidSchedule.strict_birth
#print axioms DRGPR.PaidSchedule.registered_union_births
#print axioms DRGPR.PaidSchedule.paid_prefix
#print axioms DRGPR.PaidSchedule.every_registration_prefix
#print axioms DRGPR.PaidSchedule.total_hard_cost
#print axioms DRGPR.PaidSchedule.paid_growing_regret
