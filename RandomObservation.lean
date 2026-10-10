import DRGPR

/-! Finite observation contract with a history-dependent active support.
Inactive identities have zero recommendation probability and zero estimates.
They incur no inverse-probability burden. Conditional target correctness is
assumed only as a model contract, not inferred from positive observation support. -/
noncomputable section
open scoped BigOperators
namespace DRGPR.RandomObservation

structure Round (I O : Type*) [Fintype I] [Fintype O] where
  p : I → ℝ
  p_nonneg : ∀ i, 0 ≤ p i
  p_sum : ∑ i, p i = 1
  kernel : I → O → ℝ
  kernel_nonneg : ∀ i o, 0 ≤ kernel i o
  kernel_sum : ∀ i, ∑ o, kernel i o = 1
  accepted : I → O → Bool
  score : I → O → ℝ
  d : ℝ
  d_nonneg : 0 ≤ d
  score_nonneg : ∀ i o, 0 ≤ score i o
  score_le : ∀ i o, score i o ≤ d
  q : I → ℝ
  q_pos : ∀ i, 0 < q i
  q_def : ∀ i, ∑ o, kernel i o * (if accepted i o then 1 else 0) = q i
  loss : I → ℝ
  moment : ∀ i, ∑ o, kernel i o * (if accepted i o then score i o else 0)
    = q i * loss i

variable {I O : Type*} [Fintype I] [Fintype O]

namespace Round

def avg (D : Round I O) (f : I → O → ℝ) : ℝ :=
  ∑ i, D.p i * ∑ o, D.kernel i o * f i o

def usedScore (D : Round I O) (i : I) (o : O) : ℝ :=
  if D.accepted i o then D.score i o else 0

def estimate [DecidableEq I] (D : Round I O) (draw : I) (o : O) (i : I) : ℝ :=
  if draw = i then D.usedScore draw o / (D.p i * D.q i) else 0

theorem joint_nonneg (D : Round I O) (i : I) (o : O) :
    0 ≤ D.p i * D.kernel i o :=
  mul_nonneg (D.p_nonneg i) (D.kernel_nonneg i o)

theorem avg_one (D : Round I O) : D.avg (fun _ _ => 1) = 1 := by
  simp [avg, D.kernel_sum, D.p_sum]

theorem avg_add (D : Round I O) (f g : I → O → ℝ) :
    D.avg (fun i o => f i o + g i o) = D.avg f + D.avg g := by
  simp [avg, mul_add, Finset.sum_add_distrib]

theorem avg_sub (D : Round I O) (f g : I → O → ℝ) :
    D.avg (fun i o => f i o - g i o) = D.avg f - D.avg g := by
  simp [avg, mul_sub, Finset.sum_sub_distrib]

theorem avg_const_mul (D : Round I O) (a : ℝ) (f : I → O → ℝ) :
    D.avg (fun i o => a * f i o) = a * D.avg f := by
  simp only [avg, Finset.mul_sum]
  congr 1
  funext i
  congr 1
  funext o
  ring

theorem avg_sum {J : Type*} [Fintype J] (D : Round I O) (f : J → I → O → ℝ) :
    D.avg (fun i o => ∑ j, f j i o) = ∑ j, D.avg (f j) := by
  simp only [avg, Finset.mul_sum]
  calc
    (∑ i, ∑ o, ∑ j, D.p i * (D.kernel i o * f j i o))
      = ∑ i, ∑ j, ∑ o, D.p i * (D.kernel i o * f j i o) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
    _ = ∑ j, ∑ i, ∑ o, D.p i * (D.kernel i o * f j i o) := by
      rw [Finset.sum_comm]

theorem avg_mono (D : Round I O) (f g : I → O → ℝ)
    (h : ∀ i o, f i o ≤ g i o) : D.avg f ≤ D.avg g := by
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_left _ (D.p_nonneg i)
  exact Finset.sum_le_sum fun o _ =>
    mul_le_mul_of_nonneg_left (h i o) (D.kernel_nonneg i o)

theorem used_nonneg (D : Round I O) (i : I) (o : O) :
    0 ≤ D.usedScore i o := by
  simp only [usedScore]
  split_ifs
  · exact D.score_nonneg i o
  · exact le_refl 0

theorem used_le (D : Round I O) (i : I) (o : O) :
    D.usedScore i o ≤ D.d := by
  simp only [usedScore]
  split_ifs
  · exact D.score_le i o
  · exact D.d_nonneg

theorem estimate_nonneg [DecidableEq I] (D : Round I O) (draw i : I) (o : O) :
    0 ≤ D.estimate draw o i := by
  simp only [estimate]
  split_ifs
  · exact div_nonneg (used_nonneg D draw o) (mul_nonneg (D.p_nonneg i) (D.q_pos i).le)
  · exact le_refl 0

theorem used_second (D : Round I O) (i : I) :
    (∑ o, D.kernel i o * (D.usedScore i o)^2) ≤ D.q i * D.d^2 := by
  calc
    (∑ o, D.kernel i o * (D.usedScore i o)^2)
      ≤ ∑ o, D.kernel i o * ((if D.accepted i o then 1 else 0) * D.d^2) := by
        apply Finset.sum_le_sum
        intro o _
        apply mul_le_mul_of_nonneg_left _ (D.kernel_nonneg i o)
        simp only [usedScore]
        split_ifs
        · simp only [one_mul]
          exact DRGPR.square_bounded _ _ (D.score_nonneg i o) (D.score_le i o)
        · simp
    _ = (∑ o, D.kernel i o * (if D.accepted i o then 1 else 0)) * D.d^2 := by
      simp only [Finset.sum_mul, mul_assoc]
    _ = D.q i * D.d^2 := by rw [D.q_def]

theorem estimate_mean [DecidableEq I] (D : Round I O) (i : I) (hp : 0 < D.p i) :
    D.avg (fun draw o => D.estimate draw o i) = D.loss i := by
  classical
  have h : D.avg (fun draw o => D.estimate draw o i) =
      D.p i * ((∑ o, D.kernel i o * D.usedScore i o) / (D.p i * D.q i)) := by
    simp [avg, estimate, ← mul_div_assoc, ← Finset.sum_div]
  rw [h]
  have hm : (∑ o, D.kernel i o * D.usedScore i o) = D.q i * D.loss i := D.moment i
  rw [hm]
  field_simp [hp.ne', (D.q_pos i).ne']
  <;> ring

theorem estimate_second [DecidableEq I] (D : Round I O) (i : I) (hp : 0 < D.p i) :
    D.avg (fun draw o => (D.estimate draw o i)^2)
      ≤ D.d^2 / (D.p i * D.q i) := by
  classical
  have he : D.avg (fun draw o => (D.estimate draw o i)^2) =
      D.p i / ((D.p i)^2 * (D.q i)^2) *
        (∑ o, D.kernel i o * (D.usedScore i o)^2) := by
    simp [avg, estimate, div_pow, mul_pow, ← mul_div_assoc, ← Finset.sum_div]
    ring
  rw [he]
  exact DRGPR.importance_second_bound _ _ _ _ hp (D.q_pos i) (used_second D i)

theorem estimate_zero [DecidableEq I] (D : Round I O) (i : I) (hp : D.p i = 0)
    (draw : I) (o : O) : D.estimate draw o i = 0 := by
  simp [estimate, hp]

def burden (D : Round I O) : ℝ := ∑ i, if 0 < D.p i then 1 / D.q i else 0

theorem burden_nonneg (D : Round I O) : 0 ≤ D.burden := by
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · exact (div_pos (by norm_num) (D.q_pos i)).le
  · rfl

theorem weighted_second [DecidableEq I] (D : Round I O) :
    D.avg (fun draw o => ∑ i, D.p i * (D.estimate draw o i)^2)
      ≤ D.d^2 * D.burden := by
  rw [avg_sum]
  simp_rw [avg_const_mul]
  unfold burden
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  by_cases hp : 0 < D.p i
  · rw [if_pos hp]
    have h := mul_le_mul_of_nonneg_left (estimate_second D i hp) (D.p_nonneg i)
    calc
      _ ≤ D.p i * (D.d^2 / (D.p i * D.q i)) := h
      _ = D.d^2 * (1/D.q i) := by field_simp [hp.ne', (D.q_pos i).ne'] <;> ring
  · have hz : D.p i = 0 := le_antisymm (le_of_not_gt hp) (D.p_nonneg i)
    simp [hz]

theorem learner_linear [DecidableEq I] (D : Round I O) :
    D.avg (fun draw o => ∑ i, D.p i * D.estimate draw o i)
      = D.avg (fun draw _ => D.loss draw) := by
  rw [avg_sum]
  simp_rw [avg_const_mul]
  have he (i : I) : D.p i * D.avg (fun draw o => D.estimate draw o i) =
      D.p i * D.loss i := by
    by_cases hp : 0 < D.p i
    · rw [estimate_mean D i hp]
    · have hz : D.p i = 0 := le_antisymm (le_of_not_gt hp) (D.p_nonneg i)
      simp [hz]
  simp_rw [he]
  simp [avg, ← Finset.sum_mul, D.kernel_sum]

theorem comparator_linear [DecidableEq I] (D : Round I O) (v : I) (hv : 0 < D.p v) :
    D.avg (fun draw o => D.estimate draw o v) = D.avg (fun _ _ => D.loss v) := by
  rw [estimate_mean D v hv]
  simp [avg, ← Finset.sum_mul, D.kernel_sum, D.p_sum]

theorem regret_linear [DecidableEq I] (D : Round I O) (v : I) (hv : 0 < D.p v) :
    D.avg (fun draw o => (∑ i, D.p i * D.estimate draw o i) - D.estimate draw o v)
      = D.avg (fun draw _ => D.loss draw - D.loss v) := by
  rw [avg_sub, learner_linear, comparator_linear D v hv, ← avg_sub]

end Round
end DRGPR.RandomObservation

#print axioms DRGPR.RandomObservation.Round.estimate_mean
#print axioms DRGPR.RandomObservation.Round.estimate_second
#print axioms DRGPR.RandomObservation.Round.weighted_second
#print axioms DRGPR.RandomObservation.Round.regret_linear
#print axioms DRGPR.RandomObservation.Round.joint_nonneg
#print axioms DRGPR.RandomObservation.Round.avg_one
#print axioms DRGPR.RandomObservation.Round.avg_add
#print axioms DRGPR.RandomObservation.Round.avg_sub
#print axioms DRGPR.RandomObservation.Round.avg_const_mul
#print axioms DRGPR.RandomObservation.Round.avg_sum
#print axioms DRGPR.RandomObservation.Round.avg_mono
#print axioms DRGPR.RandomObservation.Round.used_nonneg
#print axioms DRGPR.RandomObservation.Round.used_le
#print axioms DRGPR.RandomObservation.Round.estimate_nonneg
#print axioms DRGPR.RandomObservation.Round.used_second
#print axioms DRGPR.RandomObservation.Round.learner_linear
#print axioms DRGPR.RandomObservation.Round.comparator_linear


#print axioms DRGPR.RandomObservation.Round.estimate_zero
#print axioms DRGPR.RandomObservation.Round.burden_nonneg
