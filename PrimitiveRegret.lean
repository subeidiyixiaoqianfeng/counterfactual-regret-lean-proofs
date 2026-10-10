import BlockMacroEncoding
import ComparatorEncoding

noncomputable section
open scoped BigOperators
namespace DRGPR.PrimitiveRegret
open SupportedInformation HistoryAppend PrimitiveRun BlockFlattening BlockMacroEncoding
variable {I : Type} [Fintype I] [DecidableEq I]

theorem learner_append (n : ℕ) (e : Hist (I → Bool) n) (a : Hist (I × Bool) n) :
    ∀ m (g : Hist (I → Bool) m) (c : Hist (I × Bool) m),
    ObliviousMinimax.learnerTotal (n+m)
      (ObliviousFactorization.zip (n+m) (append n e m g) (append n a m c))=
      ObliviousMinimax.learnerTotal n (ObliviousFactorization.zip n e a)+
      ObliviousMinimax.learnerTotal m (ObliviousFactorization.zip m g c) := by
  intro m
  induction m with
  | zero => intro g c; simp [append,ObliviousMinimax.learnerTotal,cumulative]
  | succ m ih =>
    intro g c
    change ObliviousMinimax.learnerTotal (n+m)
      (ObliviousFactorization.zip (n+m) (append n e m g.1) (append n a m c.1))+
      ObliviousInformation.loss (g.2 c.2.1)=_
    rw [ih]
    simp only [ObliviousMinimax.learnerTotal,cumulative,ObliviousFactorization.zip,add_assoc]

theorem comparator_append (i : I) (n : ℕ) (e : Hist (I → Bool) n) :
    ∀ m (g : Hist (I → Bool) m), ObliviousMinimax.tableTotal i (n+m) (append n e m g)=
      ObliviousMinimax.tableTotal i n e+ObliviousMinimax.tableTotal i m g := by
  intro m
  induction m with
  | zero => intro g; simp [append,ObliviousMinimax.tableTotal,cumulative]
  | succ m ih =>
    intro g
    change ObliviousMinimax.tableTotal i (n+m) (append n e m g.1)+ObliviousInformation.loss (g.2 i)=_
    rw [ih]
    simp only [ObliviousMinimax.tableTotal,cumulative,add_assoc]

theorem gap_exact (d : ℕ) (e : ℕ → Hist (I → Bool) (d+1))
    (q η : ℝ) (hq : 0 < q) (hq1 : q ≤ 1) (hη : 0 < η) (p : FiniteController.Dist I) (j : I) :
    ∀ r (h : Hist (I × (Fin (d+1) → Bool)) r),
    cumulative ((macroAlgorithm d e q η hq hq1 hη p).actualGap (fun _ _ => j)) r h =
      ObliviousMinimax.learnerTotal (length (d+1) r)
        (ObliviousFactorization.zip (length (d+1) r) (flatten (d+1) r (tables d e r))
          (flatten (d+1) r (encode d r h))) -
      ObliviousMinimax.tableTotal j (length (d+1) r) (flatten (d+1) r (tables d e r)) := by
  intro r
  induction r with
  | zero => intro h; simp [cumulative,length,ObliviousMinimax.learnerTotal,ObliviousMinimax.tableTotal]
  | succ r ih =>
    intro h
    change cumulative _ r h.1 +
      ((∑ t, losses d e r h.2.1 t)-(∑ t, losses d e r j t)) =
      ObliviousMinimax.learnerTotal (length (d+1) r+(d+1))
        (ObliviousFactorization.zip (length (d+1) r+(d+1))
          (append (length (d+1) r) (flatten (d+1) r (tables d e r)) (d+1) (e r))
          (append (length (d+1) r) (flatten (d+1) r (encode d r h.1)) (d+1) (record d h.2))) -
      ObliviousMinimax.tableTotal j (length (d+1) r+(d+1))
        (append (length (d+1) r) (flatten (d+1) r (tables d e r)) (d+1) (e r))
    rw [ih,learner_append,comparator_append]
    unfold record
    rw [RunStateCoupling.held_base_loss]
    simp_rw [ComparatorEncoding.table_total_sum]
    unfold losses
    ring

/-- A regret bound for the primitive-transcript algorithm itself. Its
trajectory law, support, state updates and macro loss identity are all
derived in preceding lemmas, not supplied as regret premises. -/
theorem primitive_base_regret (d : ℕ) (e : ℕ → Hist (I → Bool) (d+1))
    (q η : ℝ) (hq : 0 < q) (hq1 : q ≤ 1) (hη : 0 < η)
    (p : FiniteController.Dist I) (hp : ∀ i, 0 < p.val i) (f j : I) (r : ℕ) :
    (∑ a, ObliviousFactorization.playerWeight
      (ObliviousInformation.choice (algorithm q η (d+1) p f).p q) (length (d+1) r)
      (flatten (d+1) r (tables d e r)) a *
      ObliviousMinimax.learnerTotal (length (d+1) r)
        (ObliviousFactorization.zip (length (d+1) r) (flatten (d+1) r (tables d e r)) a)) -
      ObliviousMinimax.tableTotal j (length (d+1) r) (flatten (d+1) r (tables d e r)) ≤
    -Real.log (p.val j)/η+η/2*((r:ℝ)*(Fintype.card I:ℝ)*
      (((d+1:ℕ):ℝ)^2+((d+1:ℕ):ℝ)/q)) := by
  let A := macroAlgorithm d e q η hq hq1 hη p
  have hr := GranularController.algorithm_regret q hq hq1 η hη p hp
    (fun n _ => losses d e n) (fun n _ => losses_nonneg d e n) (fun n _ => losses_le d e n) r j
  change (∑ h, pathLaw A.kernel r h*cumulative (A.actualGap (fun _ _ => j)) r h) ≤ _ at hr
  have hg := gap_exact d e q η hq hq1 hη p j r
  change ∀ h, cumulative (A.actualGap (fun _ _ => j)) r h=_ at hg
  simp_rw [hg] at hr
  simp only [mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul,A.law_normalized,one_mul,Fintype.card_fin] at hr
  rw [primitive_trajectory_law d e q η hq hq1 hη p f]
  exact hr

end DRGPR.PrimitiveRegret
#print axioms DRGPR.PrimitiveRegret.learner_append
#print axioms DRGPR.PrimitiveRegret.comparator_append
#print axioms DRGPR.PrimitiveRegret.gap_exact
#print axioms DRGPR.PrimitiveRegret.primitive_base_regret
