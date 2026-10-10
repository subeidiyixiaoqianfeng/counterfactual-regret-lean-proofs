import PrimitiveConcatenation
import RunActualCost

noncomputable section
open scoped BigOperators
namespace DRGPR.ShortRunDistribution
open SupportedInformation PrimitiveRun SingleRunCoupling HistoryFunction RunDistribution
variable {I : Type} [Fintype I] [DecidableEq I]

/-- The exact trajectory law also holds for a short final run. -/
theorem segment_expectation (q η : ℝ) (b d : ℕ) (hb : d+1 ≤ b) (p : FiniteController.Dist I) (f : I)
    (e : Hist (I → Bool) (d+1)) (g : Hist (I × Bool) (d+1) → ℝ) :
    (∑ a, ObliviousFactorization.playerWeight
      (ObliviousInformation.choice (algorithm q η b p f).p q) (d+1) e a*g a)=
    ∑ i, p.val i*(∑ x : Fin (d+1) → Bool, TableDistribution.row (fun _ => q) x*
      g (coins i (d+1) (ofFn (d+1) x))) := by
  let w := ObliviousFactorization.playerWeight
    (ObliviousInformation.choice (algorithm q η b p f).p q) (d+1) e
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
      obtain ⟨i,x,hx⟩ := supported_is_held q η b p f (d+1) e a (by omega) hb hn
      exact ha ⟨(i,x),hx.symm⟩
    change w a*g a=0
    rw [hw,zero_mul]
  change (∑ a, w a*g a)=_
  rw [he,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  have hw (x : Hist Bool (d+1)) : w (coins i (d+1) x)=
      p.val i*productWeight (fun _ => ErasedBandit.bernoulli q) (d+1) x := by
    simpa [w] using held_likelihood q η b p f i (d+1) e x hb
  simp_rw [hw,mul_assoc,← Finset.mul_sum]
  rw [bernoulli_expectation]

/-- Updating at the end of the final short run or leaving its final weights
unupdated has no effect on any emitted trajectory. This does not claim that
the two final weight vectors themselves coincide. -/
theorem cap_irrelevant (q η : ℝ) (b d : ℕ) (hb : d+1 ≤ b)
    (p : FiniteController.Dist I) (f : I) (e : Hist (I → Bool) (d+1))
    (g : Hist (I × Bool) (d+1) → ℝ) :
    (∑ a, ObliviousFactorization.playerWeight
      (ObliviousInformation.choice (algorithm q η b p f).p q) (d+1) e a*g a)=
    ∑ a, ObliviousFactorization.playerWeight
      (ObliviousInformation.choice (algorithm q η (d+1) p f).p q) (d+1) e a*g a := by
  rw [segment_expectation q η b d hb,RunDistribution.segment_expectation]

theorem actual_cost_same (q η : ℝ) (b d : ℕ) (hb : d+1 ≤ b)
    (p : FiniteController.Dist I) (f : I) (e : Hist (I → Bool) (d+1))
    (label : I → ℕ) (r previous : ℕ) :
    (∑ a, ObliviousFactorization.playerWeight
      (ObliviousInformation.choice (algorithm q η b p f).p q) (d+1) e a*
        RunActualCost.cost label r d previous e a)=
    ∑ a, ObliviousFactorization.playerWeight
      (ObliviousInformation.choice (algorithm q η (d+1) p f).p q) (d+1) e a*
        RunActualCost.cost label r d previous e a :=
  cap_irrelevant q η b d hb p f e _

end DRGPR.ShortRunDistribution
#print axioms DRGPR.ShortRunDistribution.segment_expectation
#print axioms DRGPR.ShortRunDistribution.cap_irrelevant
#print axioms DRGPR.ShortRunDistribution.actual_cost_same
