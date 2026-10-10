import PhaseTuning
import Mathlib.Order.Interval.Finset.Nat

noncomputable section
open scoped BigOperators
namespace DRGPR.WindowLedger

theorem run_count {R : Type*} [Fintype R]
    (length : R → ℕ) (T b N : ℕ) (hb : 0 < b)
    (hcap : ∀ r, length r ≤ b) (htotal : ∑ r, length r ≤ T)
    (hextra : (∑ r, if length r < b then (1:ℝ) else 0) ≤ N+1) :
    (Fintype.card R:ℝ) ≤ Nat.ceil ((T:ℝ)/b)+N+1 := by
  have hbR : (0:ℝ) < b := Nat.cast_pos.mpr hb
  have hlocal (r : R) : (1:ℝ) ≤ (length r:ℝ)/b+(if length r < b then 1 else 0) := by
    by_cases h : length r < b
    · rw [if_pos h]
      have := div_nonneg (Nat.cast_nonneg (length r)) hbR.le
      linarith
    · have heq : length r=b := Nat.le_antisymm (hcap r) (Nat.le_of_not_lt h)
      simp [heq, hbR.ne']
  have hsum := Finset.sum_le_sum (fun r (_ : r ∈ (Finset.univ : Finset R)) => hlocal r)
  simp only [Finset.sum_add_distrib, ← Finset.sum_div, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one] at hsum
  have hsumR : (∑ r, (length r:ℝ)) ≤ (T:ℝ) := by exact_mod_cast htotal
  have hquot := div_le_div_of_nonneg_right hsumR hbR.le
  have hceil := Nat.le_ceil ((T:ℝ)/b)
  linarith

theorem prefix_count {R : Type*} [Fintype R]
    (length : R → ℕ) (T b N H : ℕ) (hb : 0 < b)
    (hcap : ∀ r, length r ≤ b) (htotal : ∑ r, length r ≤ T)
    (hextra : (∑ r, if length r < b then (1:ℝ) else 0) ≤ N+1) :
    (∑ r, (min H (length r):ℝ)) ≤ (H:ℝ)*(Nat.ceil ((T:ℝ)/b)+N+1) := by
  have hr := run_count length T b N hb hcap htotal hextra
  calc
    _ ≤ ∑ _r : R, (H:ℝ) := Finset.sum_le_sum fun r _ => by exact_mod_cast min_le_left H (length r)
    _ = (H:ℝ)*(Fintype.card R:ℝ) := by simp; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hr (Nat.cast_nonneg H)

def windows (S : Finset ℕ) (H : ℕ) : Finset ℕ :=
  Finset.range H ∪ S.biUnion (fun s => Finset.Ico s (s+H))

theorem window_card (S : Finset ℕ) (H : ℕ) :
    (windows S H).card ≤ H*(S.card+1) := by
  have hu := Finset.card_union_le (Finset.range H) (S.biUnion (fun s => Finset.Ico s (s+H)))
  have hb : (S.biUnion (fun s => Finset.Ico s (s+H))).card ≤
      ∑ s ∈ S, (Finset.Ico s (s+H)).card := Finset.card_biUnion_le
  simp only [Nat.card_Ico, Nat.add_sub_cancel_left, Finset.sum_const, smul_eq_mul] at hb
  simp only [Finset.card_range] at hu
  dsimp [windows]
  nlinarith

theorem change_witness {I : Type*} (u : ℕ → I) (a t : ℕ) (hat : a ≤ t)
    (hne : u a ≠ u t) : ∃ s, a < s ∧ s ≤ t ∧ u s ≠ u (s-1) := by
  induction t with
  | zero =>
    have ha : a=0 := by omega
    subst a
    exact False.elim (hne rfl)
  | succ t ih =>
    by_cases ha : a=t+1
    · subst a; exact False.elim (hne rfl)
    have hat' : a ≤ t := by omega
    by_cases hs : u (t+1)=u t
    · obtain ⟨s,h₁,h₂,h₃⟩ := ih hat' (by simpa [hs] using hne)
      exact ⟨s,h₁,by omega,h₃⟩
    · exact ⟨t+1,by omega,le_refl _,by simpa using hs⟩

def switches {I : Type*} [DecidableEq I] (u : ℕ → I) (T : ℕ) : Finset ℕ :=
  (Finset.range T).filter (fun s => 0 < s ∧ u s ≠ u (s-1))

theorem outside_window_constant {I : Type*} [DecidableEq I]
    (u : ℕ → I) (T H t k : ℕ) (ht : t < T) (hk : k ≤ H)
    (hgood : t ∉ windows (switches u T) H) : u (t-k)=u t := by
  have hH : H ≤ t := by
    by_contra hn
    apply hgood
    exact Finset.mem_union_left _ (Finset.mem_range.mpr (by omega))
  by_contra hne
  obtain ⟨s,hslo,hshi,hsne⟩ := change_witness u (t-k) t (Nat.sub_le _ _) hne
  have hsp : 0 < s := by omega
  have hsT : s < T := lt_of_le_of_lt hshi ht
  have hsin : s ∈ switches u T := by simp [switches,hsT,hsp,hsne]
  apply hgood
  apply Finset.mem_union_right
  apply Finset.mem_biUnion.mpr
  exact ⟨s,hsin,Finset.mem_Ico.mpr ⟨hshi,by omega⟩⟩

theorem bounded_bad_set {J : Type*} [DecidableEq J]
    (times bad : Finset J) (x y : J → ℝ)
    (hx : ∀ t ∈ times, x t ≤ 1) (hy : ∀ t ∈ times, 0 ≤ y t)
    (heq : ∀ t ∈ times, t ∉ bad → x t=y t) :
    (∑ t ∈ times, (x t-y t)) ≤ (bad.card:ℝ) := by
  calc
    _ ≤ ∑ t ∈ times, (if t ∈ bad then (1:ℝ) else 0) := by
      apply Finset.sum_le_sum
      intro t ht
      by_cases hb : t ∈ bad
      · rw [if_pos hb]; linarith [hx t ht,hy t ht]
      · simp [hb,heq t ht hb]
    _ = ((times.filter (fun t => t ∈ bad)).card:ℝ) := by
      simp [Finset.filter_mem_eq_inter]
    _ ≤ _ := by
      exact_mod_cast Finset.card_le_card (show times.filter (fun t => t ∈ bad) ⊆ bad from
        fun t ht => (Finset.mem_filter.mp ht).2)

theorem finite_memory_comparison {I : Type*} [DecidableEq I]
    (u : ℕ → I) (T H : ℕ) (f : ℕ → (Fin (H+1) → I) → ℝ)
    (hf0 : ∀ t x, 0 ≤ f t x) (hf1 : ∀ t x, f t x ≤ 1) :
    (∑ t ∈ Finset.range T,
      (f t (fun _ => u t)-f t (fun k => u (t-k.val)))) ≤ (H:ℝ)*((switches u T).card+1) := by
  have h := bounded_bad_set (Finset.range T) (windows (switches u T) H)
    (fun t => f t (fun _ => u t)) (fun t => f t (fun k => u (t-k.val)))
    (fun t _ => hf1 _ _) (fun t _ => hf0 _ _) (by
      intro t ht hg
      apply congrArg (f t)
      funext k
      exact (outside_window_constant u T H t k.val (Finset.mem_range.mp ht) (by omega) hg).symm)
  have hc : ((windows (switches u T) H).card:ℝ) ≤ (H:ℝ)*((switches u T).card+1) := by
    exact_mod_cast window_card (switches u T) H
  exact le_trans h hc

end DRGPR.WindowLedger
#print axioms DRGPR.WindowLedger.run_count
#print axioms DRGPR.WindowLedger.prefix_count
#print axioms DRGPR.WindowLedger.window_card
#print axioms DRGPR.WindowLedger.change_witness
#print axioms DRGPR.WindowLedger.outside_window_constant
#print axioms DRGPR.WindowLedger.bounded_bad_set
#print axioms DRGPR.WindowLedger.finite_memory_comparison
