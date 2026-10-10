import PrimitiveTaskRegret

noncomputable section
open scoped BigOperators
namespace DRGPR.PrimitiveTailRegret
open SupportedInformation HistoryAppend HistoryLookup RunActualCost
open BlockFlattening BlockMacroEncoding PrimitiveRegret PrimitiveTaskRegret
variable {I : Type} [Fintype I] [DecidableEq I]

theorem appended_task_bound (label : I → ℕ) (n : ℕ) (e : Hist (I → Bool) n)
    (a : Hist (I × Bool) n) (m : ℕ) (tail : Hist (I → Bool) m) (i : I) (x : Hist Bool m) :
    taskTotal label (n+m) (append n e m tail) (append n a m (SingleRunCoupling.coins i m x)) ≤
      taskTotal label n e a+((m:ℝ)+1)/2 := by
  have hs : ((WindowLedger.switches (labels label (n+m)
      (append n a m (SingleRunCoupling.coins i m x))) (n+m)).card:ℝ) ≤
      (WindowLedger.switches (labels label n a) n).card+1 := by
    exact_mod_cast append_held_switch_bound label n a m i x
  have hl := (ObliviousMinimax.total_bounds
    (fun z : ObliviousInformation.Event I => ObliviousInformation.loss (z.1 z.2.1))
    (fun _ => ObliviousMinimax.loss_bounds _) m
    (ObliviousFactorization.zip m tail (SingleRunCoupling.coins i m x))).2
  unfold taskTotal
  rw [learner_append]
  change ObliviousMinimax.learnerTotal m _ ≤ (m:ℝ) at hl
  linarith

/-- The short tail is averaged over actual action and erasure coins. It does
not require equality between a short-run final weight and a full-run weight. -/
theorem tail_task_expectation (label : I → ℕ) (d r s : ℕ) (hs : s+1 ≤ d+1)
    (e : ℕ → Hist (I → Bool) (d+1)) (tail : Hist (I → Bool) (s+1))
    (q η : ℝ) (hq : 0 < q) (hq1 : q ≤ 1) (hη : 0 < η)
    (p : FiniteController.Dist I) (f : I) :
    (∑ a, ObliviousFactorization.playerWeight
      (ObliviousInformation.choice (PrimitiveRun.algorithm q η (d+1) p f).p q)
      (length (d+1) r+(s+1)) (append (length (d+1) r)
        (flatten (d+1) r (tables d e r)) (s+1) tail) a *
      taskTotal label (length (d+1) r+(s+1))
        (append (length (d+1) r) (flatten (d+1) r (tables d e r)) (s+1) tail) a) ≤
    (∑ a, ObliviousFactorization.playerWeight
      (ObliviousInformation.choice (PrimitiveRun.algorithm q η (d+1) p f).p q) (length (d+1) r)
      (flatten (d+1) r (tables d e r)) a *
      taskTotal label (length (d+1) r) (flatten (d+1) r (tables d e r)) a)+((s+1:ℕ)+1:ℝ)/2 := by
  rw [PhaseFlattening.complete_phase_law q η (d+1) r s hs]
  rw [expectation_exact d e q η hq hq1 hη p f]
  rw [primitive_trajectory_law d e q η hq hq1 hη p f]
  let A := macroAlgorithm d e q η hq hq1 hη p
  have hc (h : Hist (I × (Fin (d+1) → Bool)) r) :
      (∑ i, (blockState q η (d+1) p f r (tables d e r) (encode d r h)).distribution.val i *
        ∑ x : Fin (s+1) → Bool, TableDistribution.row (fun _ => q) x *
          taskTotal label (length (d+1) r+(s+1))
            (append (length (d+1) r) (flatten (d+1) r (tables d e r)) (s+1) tail)
            (append (length (d+1) r) (flatten (d+1) r (encode d r h)) (s+1)
              (SingleRunCoupling.coins i (s+1) (HistoryFunction.ofFn (s+1) x)))) ≤
      taskTotal label (length (d+1) r) (flatten (d+1) r (tables d e r))
        (flatten (d+1) r (encode d r h))+((s+1:ℕ)+1:ℝ)/2 := by
    let p' := (blockState q η (d+1) p f r (tables d e r) (encode d r h)).distribution
    have hh := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset I)) =>
      mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum (fun x (_ : x ∈ (Finset.univ : Finset (Fin (s+1) → Bool))) =>
          mul_le_mul_of_nonneg_left (appended_task_bound label (length (d+1) r)
            (flatten (d+1) r (tables d e r)) (flatten (d+1) r (encode d r h)) (s+1) tail i
            (HistoryFunction.ofFn (s+1) x))
            (TableDistribution.row_nonneg (fun _ : Fin (s+1) => q) (fun _ => hq.le) (fun _ => hq1) x)))
        (p'.nonneg i))
    simp only [← Finset.sum_mul,TableDistribution.row_normalized,one_mul,p'.sum_one] at hh
    exact hh
  have hh := Finset.sum_le_sum (fun h (_ : h ∈ (Finset.univ : Finset (Hist (I × (Fin (d+1) → Bool)) r))) =>
    mul_le_mul_of_nonneg_left (hc h) (A.law_nonneg r h))
  simp only [mul_add,Finset.sum_add_distrib,← Finset.sum_mul,A.law_normalized,one_mul] at hh
  exact hh

/-- Arbitrary nonempty horizons are covered by complete runs plus a short
tail. The tail ledger is explicit, bounded by (b+1)/2, and paid only once. -/
theorem primitive_arbitrary_horizon (label : I → ℕ) (d r s : ℕ) (hs : s+1 ≤ d+1)
    (e : ℕ → Hist (I → Bool) (d+1)) (tail : Hist (I → Bool) (s+1))
    (q η : ℝ) (hq : 0 < q) (hq1 : q ≤ 1) (hη : 0 < η)
    (p : FiniteController.Dist I) (hp : ∀ i, 0 < p.val i) (f j : I) :
    (∑ a, ObliviousFactorization.playerWeight
      (ObliviousInformation.choice (PrimitiveRun.algorithm q η (d+1) p f).p q)
      (length (d+1) r+(s+1)) (append (length (d+1) r)
        (flatten (d+1) r (tables d e r)) (s+1) tail) a *
      taskTotal label (length (d+1) r+(s+1))
        (append (length (d+1) r) (flatten (d+1) r (tables d e r)) (s+1) tail) a) -
      ObliviousMinimax.tableTotal j (length (d+1) r+(s+1))
        (append (length (d+1) r) (flatten (d+1) r (tables d e r)) (s+1) tail)/2 ≤
    (-Real.log (p.val j)/η+η/2*((r:ℝ)*(Fintype.card I:ℝ)*
      (((d+1:ℕ):ℝ)^2+((d+1:ℕ):ℝ)/q))+(r:ℝ)+(s+1:ℕ)+1)/2 := by
  have ht := tail_task_expectation label d r s hs e tail q η hq hq1 hη p f
  have hr := primitive_task_regret label d e q η hq hq1 hη p hp f j r
  have hc := (ObliviousMinimax.total_bounds
    (fun row : I → Bool => ObliviousInformation.loss (row j))
    (fun _ => ObliviousMinimax.loss_bounds _) (s+1) tail).1
  change 0 ≤ ObliviousMinimax.tableTotal j (s+1) tail at hc
  rw [comparator_append]
  linarith

end DRGPR.PrimitiveTailRegret
#print axioms DRGPR.PrimitiveTailRegret.appended_task_bound
#print axioms DRGPR.PrimitiveTailRegret.tail_task_expectation
#print axioms DRGPR.PrimitiveTailRegret.primitive_arbitrary_horizon
