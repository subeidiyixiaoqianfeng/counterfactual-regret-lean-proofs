import PhaseAlgorithm
import WindowLedger

noncomputable section
open scoped BigOperators
namespace DRGPR.PhaseSwitching
open PhaseSchedule HistoryLookup WindowLedger PhaseAlgorithm SupportedInformation
variable {I : Type} [Fintype I] [DecidableEq I]

theorem quotient_change_at_multiple (t b : ℕ) (hb : 0 < b)
    (hne : t/b ≠ (t-1)/b) : t%b=0 := by
  by_contra hn
  have hr := Nat.mod_lt t hb
  have ht := Nat.mod_add_div t b
  rw [Nat.mul_comm b (t/b)] at ht
  have he : (t-1)/b=t/b := (Nat.div_eq_iff hb).mpr ⟨by omega,by omega⟩
  exact hne he.symm

theorem held_switch_card (c : ℕ → I) (T b : ℕ) (hb : 0 < b) :
    (switches (fun t => c (t/b)) T).card ≤ T/b+1 := by
  have hm (t : ℕ) (ht : t ∈ switches (fun t => c (t/b)) T) : t%b=0 := by
    have h := (Finset.mem_filter.mp ht).2.2
    apply quotient_change_at_multiple t b hb
    intro he
    exact h (congrArg c he)
  have hc := Finset.card_le_card_of_injOn (fun t : ℕ => t/b)
    (s := switches (fun t => c (t/b)) T) (t := Finset.range (T/b+1))
    (fun t ht => Finset.mem_range.mpr (Nat.lt_succ_of_le
      (Nat.div_le_div_right (Nat.le_of_lt (Finset.mem_range.mp (Finset.mem_filter.mp ht).1)))))
    (by
      intro t ht u hu he
      have htm := Nat.mod_add_div t b
      have hum := Nat.mod_add_div u b
      dsimp only at he
      rw [hm t ht] at htm
      rw [hm u hu,← he] at hum
      omega)
  simpa using hc

theorem held_switch_bound (c : ℕ → I) (T b : ℕ) (hb : 0 < b) :
    ((switches (fun t => c (t/b)) T).card:ℝ) ≤ (T:ℝ)/b+1 := by
  have hc : ((switches (fun t => c (t/b)) T).card:ℝ) ≤ (T/b:ℕ)+1 := by
    exact_mod_cast held_switch_card c T b hb
  have hbR : (0:ℝ) < b := Nat.cast_pos.mpr hb
  have hd : ((T/b:ℕ):ℝ) ≤ (T:ℝ)/b := by
    apply (le_div_iff₀ hbR).mpr
    exact_mod_cast Nat.div_mul_le_self T b
  linarith

def choices (T : ℕ) (h : Hist (I × (Fin T → Bool)) T) (fallback : I) (r : ℕ) : I :=
  if hr : r < T then (lookup T h ⟨r,hr⟩).1 else fallback

def played (T b : ℕ) (h : Hist (I × (Fin T → Bool)) T) (fallback : I) (t : ℕ) : I :=
  choices T h fallback (t/b)

theorem played_agrees (T b : ℕ) (h : Hist (I × (Fin T → Bool)) T) (fallback : I) (t : Fin T) :
    played T b h fallback t.val=(lookup T h (runOf T b t)).1 := by
  simp [played,choices,runOf,lt_of_le_of_lt (Nat.div_le_self t.val b) t.isLt]

def taskTotal (T b : ℕ) (l : I → Fin T → ℝ)
    (h : Hist (I × (Fin T → Bool)) T) (fallback : I) : ℝ :=
  (learnerTotal T b l h+((switches (played T b h fallback) T).card:ℝ))/2

theorem pathwise_task_bound (T b : ℕ) (hb : 0 < b) (l : I → Fin T → ℝ)
    (h : Hist (I × (Fin T → Bool)) T) (fallback j : I) :
    taskTotal T b l h fallback-comparatorTotal T l j/2 ≤
      (learnerTotal T b l h-comparatorTotal T l j)/2+((T:ℝ)/b+1)/2 := by
  have hs := held_switch_bound (choices T h fallback) T b hb
  change ((switches (played T b h fallback) T).card:ℝ) ≤ (T:ℝ)/b+1 at hs
  dsimp only [taskTotal]
  linarith

theorem expected_task_regret (T b : ℕ) (hb : 0 < b) (q η : ℝ)
    (hq : 0 < q) (hq1 : q ≤ 1) (hη : 0 < η)
    (hK : (0:ℝ) < Fintype.card I) (l : I → Fin T → ℝ)
    (hl : ∀ i t, 0 ≤ l i t) (hl1 : ∀ i t, l i t ≤ 1) (fallback j : I) :
    let A := algorithm T b q η hq hq1 hη hK l hl hl1
    (∑ h, pathLaw A.kernel T h*taskTotal T b l h fallback)-comparatorTotal T l j/2 ≤
      (Real.log (Fintype.card I)/η+η/2*((Fintype.card I:ℝ)*((b:ℝ)+1/q)*T)
        +(T:ℝ)/b+1)/2 := by
  let A := algorithm T b q η hq hq1 hη hK l hl hl1
  have hp := Finset.sum_le_sum (fun h (_ : h ∈ (Finset.univ : Finset (Hist (I × (Fin T → Bool)) T))) =>
    mul_le_mul_of_nonneg_left (pathwise_task_bound T b hb l h fallback j) (A.law_nonneg T h))
  have hn := A.law_normalized T
  simp only [mul_add,mul_sub,← mul_div_assoc,Finset.sum_add_distrib,Finset.sum_sub_distrib,
    ← Finset.sum_div,← Finset.sum_mul,hn,one_mul] at hp
  have hr := expected_base_regret T b hb q η hq hq1 hη hK l hl hl1 j
  change (∑ h, pathLaw A.kernel T h*learnerTotal T b l h)-comparatorTotal T l j ≤ _ at hr
  change (∑ h, pathLaw A.kernel T h*taskTotal T b l h fallback)-comparatorTotal T l j/2 ≤ _
  linarith

end DRGPR.PhaseSwitching
#print axioms DRGPR.PhaseSwitching.quotient_change_at_multiple
#print axioms DRGPR.PhaseSwitching.held_switch_card
#print axioms DRGPR.PhaseSwitching.held_switch_bound
#print axioms DRGPR.PhaseSwitching.played_agrees
#print axioms DRGPR.PhaseSwitching.pathwise_task_bound
#print axioms DRGPR.PhaseSwitching.expected_task_regret
