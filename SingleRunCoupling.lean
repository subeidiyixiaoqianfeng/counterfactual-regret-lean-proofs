import HistoryFunction

noncomputable section
open scoped BigOperators
namespace DRGPR.SingleRunCoupling
open SupportedInformation PrimitiveRun HistoryLookup HistoryFunction
variable {I : Type} [Fintype I] [DecidableEq I]

def coins (i : I) := FiniteSimulation.project (fun x : Bool => (i,x))

def observed (i : I) : (n : ℕ) → Hist (I → Bool) n → Hist Bool n → Hist (Option Bool) n
  | 0, _, _ => ()
  | n+1, e, x => (observed i n e.1 x.1,if x.2 then none else some (e.2 i))

theorem visible_coins (i : I) : ∀ n (e : Hist (I → Bool) n) (x : Hist Bool n),
    FiniteSimulation.project ObliviousInformation.visible n
      (ObliviousFactorization.zip n e (coins i n x))=
    FiniteSimulation.project (fun o => (i,o)) n (observed i n e x) := by
  intro n
  induction n with
  | zero => intro e x; rfl
  | succ n ih =>
    intro e x
    change (FiniteSimulation.project ObliviousInformation.visible n
      (ObliviousFactorization.zip n e.1 (coins i n x.1)),
      (i,if x.2 then none else some (e.2 i))) =
      (FiniteSimulation.project (fun o => (i,o)) n (observed i n e.1 x.1),
      (i,if x.2 then none else some (e.2 i)))
    rw [ih]

theorem observed_score (q : ℝ) (i : I) :
    ∀ n (e : Hist (I → Bool) n) (x : Hist Bool n), scoreTotal q n (observed i n e x)=
      ∑ t : Fin n, ObliviousInformation.loss ((lookup n e t) i)*GranularObservation.observed q (lookup n x t) := by
  intro n
  induction n with
  | zero => intro e x; simp [scoreTotal,cumulative]
  | succ n ih =>
    intro e x
    rw [Fin.sum_univ_castSucc]
    simp only [lookup_castSucc,lookup_last]
    change scoreTotal q n (observed i n e.1 x.1)+receivedScore q (if x.2 then none else some (e.2 i))=_
    rw [ih]
    congr 1
    cases x.2 <;> simp [receivedScore,GranularObservation.observed,div_eq_mul_inv]

theorem fallback_irrelevant_after_first (q η : ℝ) (b : ℕ) (p : FiniteController.Dist I)
    (f g : I) : ∀ n (h : Hist (I × Option Bool) (n+1)),
    state q η b p f (n+1) h=state q η b p g (n+1) h := by
  intro n
  induction n with
  | zero => intro h; rfl
  | succ n ih => intro h; change advance q η b (n+1) (state q η b p f (n+1) h.1) h.2=_; rw [ih]; rfl

theorem held_distribution (q η : ℝ) (b : ℕ) (p : FiniteController.Dist I) (f i : I)
    (t : ℕ) (h : Hist (Option Bool) t) (ht : t < b) :
    (state q η b p f t (FiniteSimulation.project (fun o => (i,o)) t h)).distribution=p := by
  cases t with
  | zero => rfl
  | succ t =>
    rw [fallback_irrelevant_after_first q η b p f i,held_state_is_actual]
    exact (held_before_end q η b p i (t+1) h ht).1

theorem held_choice (q η : ℝ) (b : ℕ) (p : FiniteController.Dist I) (f i : I)
    (t : ℕ) (h : Hist (Option Bool) t) (ht : t < b) :
    (algorithm q η b p f).p t (FiniteSimulation.project (fun o => (i,o)) t h) i=
      if t=0 then p.val i else 1 := by
  by_cases hz : t=0
  · subst t; simp [algorithm,distribution,state,initialState]
  · have hm : t%b≠0 := by rw [Nat.mod_eq_of_lt ht]; exact hz
    rw [inside_run q η b p f _ _ hm]
    cases t with
    | zero => contradiction
    | succ t =>
      rw [last_is_executed]
      simp [FiniteSimulation.project]

/-- The primitive likelihood of a held segment is its one initial arm draw
times the product of independent logging probabilities. -/
theorem held_likelihood (q η : ℝ) (b : ℕ) (p : FiniteController.Dist I) (f i : I) :
    ∀ t (e : Hist (I → Bool) t) (x : Hist Bool t), t ≤ b →
      ObliviousFactorization.playerWeight (ObliviousInformation.choice (algorithm q η b p f).p q)
        t e (coins i t x)=
      (if t=0 then 1 else p.val i)*productWeight (fun _ => ErasedBandit.bernoulli q) t x := by
  intro t
  induction t with
  | zero => intro e x ht; simp [ObliviousFactorization.playerWeight,productWeight]
  | succ t ih =>
    intro e x ht
    change ObliviousFactorization.playerWeight (ObliviousInformation.choice (algorithm q η b p f).p q)
      t e.1 (coins i t x.1)*
      ((algorithm q η b p f).p t (FiniteSimulation.project ObliviousInformation.visible t
        (ObliviousFactorization.zip t e.1 (coins i t x.1))) i*ErasedBandit.bernoulli q x.2)=_
    rw [ih e.1 x.1 (by omega),visible_coins,held_choice q η b p f i t _ (by omega)]
    simp only [productWeight,Nat.add_eq_zero_iff,one_ne_zero,and_false,ite_false]
    by_cases hz : t=0 <;> simp [hz] <;> ring

theorem score_vector_identity (q : ℝ) (i : I) (n : ℕ) (e : Hist (I → Bool) n) (x : Fin n → Bool) :
    scoreTotal q n (observed i n e (ofFn n x))=
      GranularObservation.score q (fun t => ObliviousInformation.loss ((lookup n e t) i)) x := by
  rw [observed_score]
  simp only [lookup_ofFn,GranularObservation.score]

/-- Coupling identity for every payoff of the received segment score.
No KL, regret or distribution-equivalence inequality is assumed. -/
theorem score_law (q η : ℝ) (d : ℕ) (p : FiniteController.Dist I) (f i : I)
    (e : Hist (I → Bool) (d+1)) (g : ℝ → ℝ) :
    (∑ x : Hist Bool (d+1),
      ObliviousFactorization.playerWeight (ObliviousInformation.choice (algorithm q η (d+1) p f).p q)
        (d+1) e (coins i (d+1) x)*g (scoreTotal q (d+1) (observed i (d+1) e x)))=
    p.val i*(∑ x : Fin (d+1) → Bool, TableDistribution.row (fun _ => q) x*
      g (GranularObservation.score q (fun t => ObliviousInformation.loss ((lookup (d+1) e t) i)) x)) := by
  have hk (x : Hist Bool (d+1)) := held_likelihood q η (d+1) p f i (d+1) e x le_rfl
  simp_rw [hk]
  simp only [Nat.add_eq_zero_iff,one_ne_zero,and_false,ite_false,mul_assoc,← Finset.mul_sum]
  rw [bernoulli_expectation]
  simp_rw [score_vector_identity]

end DRGPR.SingleRunCoupling
#print axioms DRGPR.SingleRunCoupling.visible_coins
#print axioms DRGPR.SingleRunCoupling.observed_score
#print axioms DRGPR.SingleRunCoupling.fallback_irrelevant_after_first
#print axioms DRGPR.SingleRunCoupling.held_distribution
#print axioms DRGPR.SingleRunCoupling.held_choice
#print axioms DRGPR.SingleRunCoupling.held_likelihood
#print axioms DRGPR.SingleRunCoupling.score_vector_identity
#print axioms DRGPR.SingleRunCoupling.score_law
