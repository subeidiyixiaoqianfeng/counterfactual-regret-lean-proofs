import StoppedEventProgram
import FiniteObservation

/-! Finite, history-dependent stopped observation law. Local accepted-score
contracts, not stopped unbiasedness, are supplied by the interface. -/
noncomputable section
open scoped BigOperators
namespace DRGPR.StoppedObservation
open DependentBlocks StoppedEventProgram
variable {I O : ℕ → Type} [∀ n, Fintype (I n)] [∀ n, Fintype (O n)]
  [∀ n, DecidableEq (I n)]

abbrev H (n : ℕ) := History (fun t => Option (I t × O t)) n

structure Protocol (I O : ℕ → Type) [∀ n, Fintype (I n)] [∀ n, Fintype (O n)] where
  go : (n : ℕ) → H (I := I) (O := O) n → Bool
  round : (n : ℕ) → H (I := I) (O := O) n → FiniteObservation.Round (I n) (O n)
  comparator : (n : ℕ) → H (I := I) (O := O) n → I n

def Protocol.event (A : Protocol I O) (n : ℕ) (h : H (I := I) (O := O) n) (x : I n × O n) : ℝ :=
  (A.round n h).p x.1 * (A.round n h).kernel x.1 x.2

def Protocol.noise (A : Protocol I O) (n : ℕ) (h : H (I := I) (O := O) n) (x : I n × O n) : ℝ :=
  let D := A.round n h
  ((∑ i, D.p i*D.estimate x.1 x.2 i)-D.estimate x.1 x.2 (A.comparator n h)) -
    (D.loss x.1-D.loss (A.comparator n h))

def Protocol.square (A : Protocol I O) (n : ℕ) (h : H (I := I) (O := O) n) (x : I n × O n) : ℝ :=
  ∑ i, (A.round n h).p i*((A.round n h).estimate x.1 x.2 i)^2

theorem Protocol.event_normalized (A : Protocol I O) (n : ℕ) (h : H n) :
    ∑ x, A.event n h x = 1 := by
  simpa [Protocol.event,FiniteObservation.Round.avg,Fintype.sum_prod_type,
    ← Finset.mul_sum] using (A.round n h).avg_one

theorem Protocol.event_nonneg (A : Protocol I O) (n : ℕ) (h : H n) (x : I n × O n) :
    0 ≤ A.event n h x := (A.round n h).joint_nonneg x.1 x.2

theorem Protocol.local_noise (A : Protocol I O) (n : ℕ) (h : H n) :
    ∑ x, A.event n h x*A.noise n h x = 0 := by
  have he := (A.round n h).regret_linear (A.comparator n h)
  have hz : (A.round n h).avg (fun i o => A.noise n h (i,o)) = 0 := by
    dsimp [Protocol.noise]
    rw [FiniteObservation.Round.avg_sub,he,sub_self]
  simpa only [Protocol.event,FiniteObservation.Round.avg,Fintype.sum_prod_type,
    Finset.mul_sum,mul_assoc] using hz

/-- The stopped moment is derived on the generated law with an absorbing
terminal state. Its activity rule can use the complete finished history. -/
theorem Protocol.stopped_unbiased (A : Protocol I O) (N : ℕ) :
    (∑ h, law (kernel A.go A.event) N h * total (score A.noise) N h) = 0 :=
  stopped_zero_moment A.go A.event A.noise A.event_normalized
    (fun n h _ => A.local_noise n h) N

theorem Protocol.local_square (A : Protocol I O) (n : ℕ) (h : H n) :
    (∑ x, A.event n h x*A.square n h x) ≤
      (A.round n h).d^2*∑ i, 1/(A.round n h).q i := by
  simpa only [Protocol.event,Protocol.square,FiniteObservation.Round.avg,
    Fintype.sum_prod_type,Finset.mul_sum,mul_assoc] using (A.round n h).weighted_second

theorem Protocol.stopped_second (A : Protocol I O) (N : ℕ) :
    (∑ h, law (kernel A.go A.event) N h * total (score A.square) N h) ≤
      ∑ n ∈ Finset.range N, ∑ h, law (kernel A.go A.event) n h *
        (if live A.go n h then (A.round n h).d^2*∑ i, 1/(A.round n h).q i else 0) := by
  rw [stopped_capacity A.go A.event A.square A.event_normalized]
  apply Finset.sum_le_sum
  intro n _
  apply Finset.sum_le_sum
  intro h _
  apply mul_le_mul_of_nonneg_left
  · cases hl : live A.go n h
    · simp
    · simpa using A.local_square n h
  · exact nonneg _ (kernel_nonneg A.go A.event A.event_nonneg) n h

end DRGPR.StoppedObservation
#print axioms DRGPR.StoppedObservation.Protocol.event_normalized
#print axioms DRGPR.StoppedObservation.Protocol.event_nonneg
#print axioms DRGPR.StoppedObservation.Protocol.local_noise
#print axioms DRGPR.StoppedObservation.Protocol.stopped_unbiased
#print axioms DRGPR.StoppedObservation.Protocol.local_square
#print axioms DRGPR.StoppedObservation.Protocol.stopped_second
