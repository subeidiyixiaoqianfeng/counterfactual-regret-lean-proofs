import SingleRunCoupling

noncomputable section
open scoped BigOperators
namespace DRGPR.RunDistribution
open SupportedInformation PrimitiveRun SingleRunCoupling HistoryFunction
variable {I : Type} [Fintype I] [DecidableEq I]

theorem coins_masks (i : I) : ∀ t (x : Hist Bool t),
    FiniteSimulation.project Prod.snd t (coins i t x)=x := by
  intro t
  induction t with
  | zero => intro x; cases x; rfl
  | succ t ih => intro x; change (FiniteSimulation.project Prod.snd t (coins i t x.1),x.2)=x; rw [ih]; rfl

theorem coins_injective (d : ℕ) :
    Function.Injective (fun z : I × Hist Bool (d+1) => coins z.1 (d+1) z.2) := by
  intro z w he
  have hi : z.1=w.1 := congrArg (fun a : Hist (I × Bool) (d+1) => a.2.1) he
  have hx := congrArg (FiniteSimulation.project Prod.snd (d+1)) he
  rw [coins_masks,coins_masks] at hx
  exact Prod.ext hi hx

theorem held_sampler (q η : ℝ) (b : ℕ) (p : FiniteController.Dist I) (f i j : I)
    (t : ℕ) (h : Hist (Option Bool) t) (ht0 : 0 < t) (ht : t < b) :
    (algorithm q η b p f).p t (FiniteSimulation.project (fun o => (i,o)) t h) j=
      if i=j then 1 else 0 := by
  have hm : t%b≠0 := by rw [Nat.mod_eq_of_lt ht]; omega
  rw [inside_run q η b p f _ _ hm]
  cases t with
  | zero => omega
  | succ t => rw [last_is_executed]; rfl

/-- Every nonzero-probability primitive trajectory of a first segment holds
its initial identity. This is a support theorem, not a restriction assumed
on the histories that happen to be summed later. -/
theorem supported_is_held (q η : ℝ) (b : ℕ) (p : FiniteController.Dist I) (f : I) :
    ∀ t (e : Hist (I → Bool) t) (a : Hist (I × Bool) t), 0 < t → t ≤ b →
      ObliviousFactorization.playerWeight (ObliviousInformation.choice (algorithm q η b p f).p q) t e a≠0 →
      ∃ i x, a=coins i t x := by
  intro t
  induction t with
  | zero => intro e a ht; omega
  | succ t ih =>
    intro e a ht hb hw
    cases t with
    | zero =>
      refine ⟨a.2.1,((),a.2.2),?_⟩
      cases a.1
      rfl
    | succ s =>
      have hp : ObliviousFactorization.playerWeight
          (ObliviousInformation.choice (algorithm q η b p f).p q) (s+1) e.1 a.1≠0 := by
        intro hz
        apply hw
        change ObliviousFactorization.playerWeight
          (ObliviousInformation.choice (algorithm q η b p f).p q) (s+1) e.1 a.1*_=0
        rw [hz,zero_mul]
      obtain ⟨i,x,hx⟩ := ih e.1 a.1 (by omega) (by omega) hp
      have hs : (algorithm q η b p f).p (s+1)
          (FiniteSimulation.project ObliviousInformation.visible (s+1)
          (ObliviousFactorization.zip (s+1) e.1 a.1)) a.2.1=
          if i=a.2.1 then 1 else 0 := by
        rw [hx,visible_coins]
        exact held_sampler q η b p f i a.2.1 (s+1) _ (by omega) (by omega)
      have hi : i=a.2.1 := by
        by_contra hn
        apply hw
        change ObliviousFactorization.playerWeight
          (ObliviousInformation.choice (algorithm q η b p f).p q) (s+1) e.1 a.1*
          ((algorithm q η b p f).p (s+1)
          (FiniteSimulation.project ObliviousInformation.visible (s+1)
          (ObliviousFactorization.zip (s+1) e.1 a.1)) a.2.1*ErasedBandit.bernoulli q a.2.2)=0
        rw [hs,if_neg hn,zero_mul,mul_zero]
      refine ⟨i,(x,a.2.2),?_⟩
      change a=(coins i (s+1) x,(i,a.2.2))
      rw [← hx,hi]
      rfl

/-- Exact equality of whole-trajectory expectations for one held segment.
The payoff may include identities, masks, loss, or the next controller state. -/
theorem segment_expectation (q η : ℝ) (d : ℕ) (p : FiniteController.Dist I) (f : I)
    (e : Hist (I → Bool) (d+1)) (g : Hist (I × Bool) (d+1) → ℝ) :
    (∑ a, ObliviousFactorization.playerWeight
      (ObliviousInformation.choice (algorithm q η (d+1) p f).p q) (d+1) e a*g a)=
    ∑ i, p.val i*(∑ x : Fin (d+1) → Bool, TableDistribution.row (fun _ => q) x*
      g (coins i (d+1) (ofFn (d+1) x))) := by
  let w := ObliviousFactorization.playerWeight
    (ObliviousInformation.choice (algorithm q η (d+1) p f).p q) (d+1) e
  have he : (∑ a, w a*g a)=
      ∑ z : I × Hist Bool (d+1), w (coins z.1 (d+1) z.2)*g (coins z.1 (d+1) z.2) := by
    symm
    apply Fintype.sum_of_injective (fun z : I × Hist Bool (d+1) => coins z.1 (d+1) z.2)
      (coins_injective d)
      (fun z => w (coins z.1 (d+1) z.2)*g (coins z.1 (d+1) z.2))
      (fun a => w a*g a) _ (fun _ => rfl)
    intro a ha
    have hw : w a=0 := by
      by_contra hn
      obtain ⟨i,x,hx⟩ := supported_is_held q η (d+1) p f (d+1) e a (by omega) le_rfl hn
      exact ha ⟨(i,x),hx.symm⟩
    change w a*g a=0
    rw [hw,zero_mul]
  change (∑ a, w a*g a)=_
  rw [he,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  have hw (x : Hist Bool (d+1)) : w (coins i (d+1) x)=
      p.val i*productWeight (fun _ => ErasedBandit.bernoulli q) (d+1) x := by
    simpa [w] using held_likelihood q η (d+1) p f i (d+1) e x le_rfl
  simp_rw [hw,mul_assoc,← Finset.mul_sum]
  rw [bernoulli_expectation]

end DRGPR.RunDistribution
#print axioms DRGPR.RunDistribution.coins_masks
#print axioms DRGPR.RunDistribution.coins_injective
#print axioms DRGPR.RunDistribution.held_sampler
#print axioms DRGPR.RunDistribution.supported_is_held
#print axioms DRGPR.RunDistribution.segment_expectation
