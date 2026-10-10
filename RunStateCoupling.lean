import RunDistribution

noncomputable section
open scoped BigOperators
namespace DRGPR.RunStateCoupling
open SupportedInformation PrimitiveRun SingleRunCoupling HistoryFunction HistoryLookup
variable {I : Type} [Fintype I] [DecidableEq I]

def endState (q η : ℝ) (d : ℕ) (p : FiniteController.Dist I) (f : I)
    (e : Hist (I → Bool) (d+1)) (a : Hist (I × Bool) (d+1)) : State I :=
  state q η (d+1) p f (d+1)
    (FiniteSimulation.project ObliviousInformation.visible (d+1) (ObliviousFactorization.zip (d+1) e a))

def macroState (q η : ℝ) (d : ℕ) (p : FiniteController.Dist I)
    (e : Hist (I → Bool) (d+1)) (i : I) (x : Fin (d+1) → Bool) : State I :=
  ⟨FiniteController.update p (GranularObservable.importance p
    (i,GranularObservation.score q (fun t => ObliviousInformation.loss ((lookup (d+1) e t) i)) x))
      η FiniteController.identityRows,i,0⟩

theorem end_state_exact (q η : ℝ) (d : ℕ) (p : FiniteController.Dist I) (f i : I)
    (e : Hist (I → Bool) (d+1)) (x : Fin (d+1) → Bool) :
    endState q η d p f e (coins i (d+1) (ofFn (d+1) x))=macroState q η d p e i x := by
  unfold endState
  rw [visible_coins,fallback_irrelevant_after_first q η (d+1) p f i,held_state_is_actual]
  have hp := held_before_end q η (d+1) p i d
    (observed i (d+1) e (ofFn (d+1) x)).1 (by omega)
  change advance q η (d+1) d (heldState q η (d+1) p i d
    (observed i (d+1) e (ofFn (d+1) x)).1)
    (i,(observed i (d+1) e (ofFn (d+1) x)).2)=_
  simp only [advance,Nat.mod_self,ite_true,hp.1,hp.2.2]
  have hs := score_vector_identity q i (d+1) e x
  change scoreTotal q d (observed i (d+1) e (ofFn (d+1) x)).1+
      receivedScore q (observed i (d+1) e (ofFn (d+1) x)).2=_ at hs
  rw [hs]
  rfl

theorem held_base_loss (i : I) : ∀ n (e : Hist (I → Bool) n) (x : Hist Bool n),
    ObliviousMinimax.learnerTotal n (ObliviousFactorization.zip n e (coins i n x))=
    ObliviousMinimax.tableTotal i n e := by
  intro n
  induction n with
  | zero => intro e x; rfl
  | succ n ih =>
    intro e x
    change ObliviousMinimax.learnerTotal n (ObliviousFactorization.zip n e.1 (coins i n x.1))+
      ObliviousInformation.loss (e.2 i)=ObliviousMinimax.tableTotal i n e.1+ObliviousInformation.loss (e.2 i)
    rw [ih]

theorem end_state_observable (q η : ℝ) (d : ℕ) (p : FiniteController.Dist I) (f : I)
    (e e' : Hist (I → Bool) (d+1)) (a a' : Hist (I × Bool) (d+1))
    (he : FiniteSimulation.project ObliviousInformation.visible (d+1) (ObliviousFactorization.zip (d+1) e a)=
      FiniteSimulation.project ObliviousInformation.visible (d+1) (ObliviousFactorization.zip (d+1) e' a')) :
    endState q η d p f e a=endState q η d p f e' a' := by
  unfold endState
  rw [he]

/-- Simultaneous equality of the next full controller state and actual
primitive base loss, tested against every real-valued continuation payoff. -/
theorem joint_state_loss_law (q η : ℝ) (d : ℕ) (p : FiniteController.Dist I) (f : I)
    (e : Hist (I → Bool) (d+1)) (G : State I → ℝ → ℝ) :
    (∑ a, ObliviousFactorization.playerWeight
      (ObliviousInformation.choice (algorithm q η (d+1) p f).p q) (d+1) e a*
      G (endState q η d p f e a)
        (ObliviousMinimax.learnerTotal (d+1) (ObliviousFactorization.zip (d+1) e a)))=
    ∑ i, p.val i*(∑ x : Fin (d+1) → Bool, TableDistribution.row (fun _ => q) x*
      G (macroState q η d p e i x) (ObliviousMinimax.tableTotal i (d+1) e)) := by
  rw [RunDistribution.segment_expectation]
  simp_rw [end_state_exact,held_base_loss]

end DRGPR.RunStateCoupling
#print axioms DRGPR.RunStateCoupling.end_state_exact
#print axioms DRGPR.RunStateCoupling.held_base_loss
#print axioms DRGPR.RunStateCoupling.end_state_observable
#print axioms DRGPR.RunStateCoupling.joint_state_loss_law
