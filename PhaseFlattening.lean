import BlockFlattening

noncomputable section
open scoped BigOperators
namespace DRGPR.PhaseFlattening
open SupportedInformation HistoryAppend PrimitiveRun PrimitiveConcatenation BlockFlattening
variable {I : Type} [Fintype I] [DecidableEq I]

/-- A full primitive phase consists of complete runs and one possibly short,
nonempty final run. Every emitted primitive transcript is included in the sum. -/
theorem complete_phase_law (q η : ℝ) (b r d : ℕ) (hd : d+1 ≤ b)
    (p : FiniteController.Dist I) (f : I)
    (e : Hist (Hist (I → Bool) b) r) (tail : Hist (I → Bool) (d+1))
    (g : Hist (I × Bool) (length b r+(d+1)) → ℝ) :
    (∑ a, ObliviousFactorization.playerWeight
      (ObliviousInformation.choice (algorithm q η b p f).p q)
      (length b r+(d+1)) (append (length b r) (flatten b r e) (d+1) tail) a*g a) =
    ∑ a : Hist (Hist (I × Bool) b) r, blockWeight q η b p f r e a *
      ∑ i, (blockState q η b p f r e a).distribution.val i *
        ∑ x : Fin (d+1) → Bool, TableDistribution.row (fun _ => q) x *
          g (append (length b r) (flatten b r a) (d+1)
            (SingleRunCoupling.coins i (d+1) (HistoryFunction.ofFn (d+1) x))) := by
  rw [sum_append]
  have he := sum_flatten b r (fun a => ∑ c,
    ObliviousFactorization.playerWeight
      (ObliviousInformation.choice (algorithm q η b p f).p q)
      (length b r+(d+1)) (append (length b r) (flatten b r e) (d+1) tail)
      (append (length b r) a (d+1) c) * g (append (length b r) a (d+1) c))
  rw [← he]
  apply Finset.sum_congr rfl
  intro a _
  have hw (c : Hist (I × Bool) (d+1)) :=
    player_weight_append q η b p f (length b r) (flatten b r e) (flatten b r a)
      (length_boundary b r) (d+1) tail c
  simp_rw [weight_flatten,state_flatten] at hw
  simp_rw [hw,mul_assoc,← Finset.mul_sum]
  congr 1
  exact ShortRunDistribution.segment_expectation q η b d hd
    (blockState q η b p f r e a).distribution (blockState q η b p f r e a).last tail
    (fun c => g (append (length b r) (flatten b r a) (d+1) c))

/-- Every positive finite horizon has this decomposition, including the
exact-multiple case, where the last run is full rather than empty. -/
theorem horizon_decomposition (T b : ℕ) (hT : 0 < T) (hb : 0 < b) :
    let r := (T-1)/b
    let d := (T-1)%b
    length b r+(d+1)=T ∧ d+1 ≤ b := by
  dsimp only
  rw [length_eq]
  have he := Nat.mod_add_div (T-1) b
  have hm := Nat.mod_lt (T-1) hb
  constructor <;> omega

end DRGPR.PhaseFlattening
#print axioms DRGPR.PhaseFlattening.complete_phase_law
#print axioms DRGPR.PhaseFlattening.horizon_decomposition
