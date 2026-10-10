import PrimitiveRegret
import SwitchConcatenation

noncomputable section
open scoped BigOperators
namespace DRGPR.PrimitiveTaskRegret
open SupportedInformation HistoryAppend HistoryLookup RunActualCost
open BlockFlattening BlockMacroEncoding PrimitiveRegret
variable {I : Type} [Fintype I] [DecidableEq I]

theorem lookup_append_left {E : Type} (n : ℕ) (h : Hist E n) :
    ∀ m (g : Hist E m) (t : Fin n),
    lookup (n+m) (append n h m g) ⟨t.val,by omega⟩=lookup n h t := by
  intro m
  induction m with
  | zero => intro g t; rfl
  | succ m ih =>
    intro g t
    change (if ht : t.val < n+m then lookup (n+m) (append n h m g.1) ⟨t.val,ht⟩ else g.2)=_
    rw [dif_pos (show t.val < n+m by omega)]
    exact ih g.1 t

theorem lookup_append_right {E : Type} (n : ℕ) (h : Hist E n) :
    ∀ m (g : Hist E m) (t : Fin m),
    lookup (n+m) (append n h m g) ⟨n+t.val,by omega⟩=lookup m g t := by
  intro m
  induction m with
  | zero => intro g t; exact Fin.elim0 t
  | succ m ih =>
    intro g t
    change (if ht : n+t.val < n+m then lookup (n+m) (append n h m g.1) ⟨n+t.val,ht⟩ else g.2)=_
    by_cases ht : t.val < m
    · simp only [lookup,dif_pos ht,dif_pos (show n+t.val < n+m by omega)]
      exact ih g.1 ⟨t.val,ht⟩
    · simp [append,lookup,ht,show ¬n+t.val < n+m by omega]

theorem switches_congr (u v : ℕ → ℕ) (n : ℕ) (h : ∀ t, t < n → u t=v t) :
    WindowLedger.switches u n=WindowLedger.switches v n := by
  ext t
  simp only [WindowLedger.switches,Finset.mem_filter,Finset.mem_range]
  by_cases ht : t < n
  · rw [h t ht,h (t-1) (by omega)]
  · simp [ht]

/-- Appending a held run adds at most one genuine change of executed identity.
It adds no within-run switches, regardless of observations or weight updates. -/
theorem append_held_switch_bound (label : I → ℕ) (n : ℕ) (a : Hist (I × Bool) n)
    (m : ℕ) (i : I) (x : Hist Bool m) :
    (WindowLedger.switches (labels label (n+m) (append n a m (SingleRunCoupling.coins i m x))) (n+m)).card ≤
      (WindowLedger.switches (labels label n a) n).card+1 := by
  let u := labels label (n+m) (append n a m (SingleRunCoupling.coins i m x))
  have hp : WindowLedger.switches u n=WindowLedger.switches (labels label n a) n := by
    apply switches_congr
    intro t ht
    dsimp only [u,labels]
    simp only [dif_pos ht,dif_pos (show t < n+m by omega)]
    exact congrArg (fun z : I × Bool => label z.1)
      (lookup_append_left n a m (SingleRunCoupling.coins i m x) ⟨t,ht⟩)
  have hs : WindowLedger.switches (fun t => u (n+t)) m=∅ := by
    have he : WindowLedger.switches (fun t => u (n+t)) m=
        WindowLedger.switches (labels label m (SingleRunCoupling.coins i m x)) m := by
      apply switches_congr
      intro t ht
      dsimp only [u,labels]
      simp only [dif_pos ht,dif_pos (show n+t < n+m by omega)]
      exact congrArg (fun z : I × Bool => label z.1)
        (lookup_append_right n a m (SingleRunCoupling.coins i m x) ⟨t,ht⟩)
    rw [he,no_internal_switch]
  change (WindowLedger.switches u (n+m)).card ≤ _
  rw [SwitchConcatenation.count_split,hp,hs,Finset.card_empty]
  unfold SwitchConcatenation.indicator
  split_ifs <;> omega

theorem encoded_switch_bound (label : I → ℕ) (d : ℕ) :
    ∀ r (h : Hist (I × (Fin (d+1) → Bool)) r),
    (WindowLedger.switches (labels label (length (d+1) r)
      (flatten (d+1) r (encode d r h))) (length (d+1) r)).card ≤ r := by
  intro r
  induction r with
  | zero => intro h; simp [length,WindowLedger.switches]
  | succ r ih =>
    intro h
    have hs := append_held_switch_bound label (length (d+1) r)
      (flatten (d+1) r (encode d r h.1)) (d+1) h.2.1 (HistoryFunction.ofFn (d+1) h.2.2)
    exact hs.trans (Nat.add_le_add_right (ih h.1) 1)

def taskTotal (label : I → ℕ) (n : ℕ) (e : Hist (I → Bool) n) (a : Hist (I × Bool) n) : ℝ :=
  (ObliviousMinimax.learnerTotal n (ObliviousFactorization.zip n e a)+
    (WindowLedger.switches (labels label n a) n).card)/2

/-- The primitive algorithm is bounded in actual task loss, not only in
importance-weighted scores. Switches are counted from its emitted identities. -/
theorem primitive_task_regret (label : I → ℕ) (d : ℕ) (e : ℕ → Hist (I → Bool) (d+1))
    (q η : ℝ) (hq : 0 < q) (hq1 : q ≤ 1) (hη : 0 < η)
    (p : FiniteController.Dist I) (hp : ∀ i, 0 < p.val i) (f j : I) (r : ℕ) :
    (∑ a, ObliviousFactorization.playerWeight
      (ObliviousInformation.choice (PrimitiveRun.algorithm q η (d+1) p f).p q) (length (d+1) r)
      (flatten (d+1) r (tables d e r)) a *
      taskTotal label (length (d+1) r) (flatten (d+1) r (tables d e r)) a) -
      ObliviousMinimax.tableTotal j (length (d+1) r) (flatten (d+1) r (tables d e r))/2 ≤
    (-Real.log (p.val j)/η+η/2*((r:ℝ)*(Fintype.card I:ℝ)*
      (((d+1:ℕ):ℝ)^2+((d+1:ℕ):ℝ)/q))+(r:ℝ))/2 := by
  let A := macroAlgorithm d e q η hq hq1 hη p
  have hr := primitive_base_regret d e q η hq hq1 hη p hp f j r
  rw [primitive_trajectory_law d e q η hq hq1 hη p f] at hr ⊢
  have hs := Finset.sum_le_sum (fun h (_ : h ∈ (Finset.univ : Finset (Hist (I × (Fin (d+1) → Bool)) r))) =>
    mul_le_mul_of_nonneg_left (show
      ((WindowLedger.switches (labels label (length (d+1) r)
        (flatten (d+1) r (encode d r h))) (length (d+1) r)).card:ℝ) ≤ (r:ℝ) from
      Nat.cast_le.mpr (encoded_switch_bound label d r h)) (A.law_nonneg r h))
  rw [← Finset.sum_mul,A.law_normalized,one_mul] at hs
  unfold taskTotal
  simp only [← mul_div_assoc,mul_add,← Finset.sum_div,Finset.sum_add_distrib]
  change (∑ h, pathLaw A.kernel r h * _)-_ ≤ _ at hr
  dsimp only [A] at hr hs
  linear_combination (1/2:ℝ)*hr+(1/2:ℝ)*hs

end DRGPR.PrimitiveTaskRegret
#print axioms DRGPR.PrimitiveTaskRegret.lookup_append_left
#print axioms DRGPR.PrimitiveTaskRegret.lookup_append_right
#print axioms DRGPR.PrimitiveTaskRegret.switches_congr
#print axioms DRGPR.PrimitiveTaskRegret.append_held_switch_bound
#print axioms DRGPR.PrimitiveTaskRegret.encoded_switch_bound
#print axioms DRGPR.PrimitiveTaskRegret.primitive_task_regret
