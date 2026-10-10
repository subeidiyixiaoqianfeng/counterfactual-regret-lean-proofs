import DRGPR

/-! A genuine finite one-round probability model.
The conditional accepted-score contract is an input, as in Assumption 2.
The importance-weighted first and second moments are derived from the
joint draw/observation law, rather than supplied as scalar cancellations.
This module does not construct the full agent trajectory. -/
noncomputable section
open scoped BigOperators
namespace DRGPR.FiniteObservation

structure Round (I O : Type*) [Fintype I] [Fintype O] where
  p : I → ℝ
  p_pos : ∀ i, 0 < p i
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
  mul_nonneg (D.p_pos i).le (D.kernel_nonneg i o)

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
  apply mul_le_mul_of_nonneg_left _ (D.p_pos i).le
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
  · exact div_nonneg (used_nonneg D draw o) (mul_pos (D.p_pos i) (D.q_pos i)).le
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

theorem estimate_mean [DecidableEq I] (D : Round I O) (i : I) :
    D.avg (fun draw o => D.estimate draw o i) = D.loss i := by
  classical
  have h : D.avg (fun draw o => D.estimate draw o i) =
      D.p i * ((∑ o, D.kernel i o * D.usedScore i o) / (D.p i * D.q i)) := by
    simp [avg, estimate, ← mul_div_assoc, ← Finset.sum_div]
  rw [h]
  have hm : (∑ o, D.kernel i o * D.usedScore i o) = D.q i * D.loss i := D.moment i
  rw [hm]
  field_simp [(D.p_pos i).ne', (D.q_pos i).ne']
  <;> ring

theorem estimate_second [DecidableEq I] (D : Round I O) (i : I) :
    D.avg (fun draw o => (D.estimate draw o i)^2)
      ≤ D.d^2 / (D.p i * D.q i) := by
  classical
  have he : D.avg (fun draw o => (D.estimate draw o i)^2) =
      D.p i / ((D.p i)^2 * (D.q i)^2) *
        (∑ o, D.kernel i o * (D.usedScore i o)^2) := by
    simp [avg, estimate, div_pow, mul_pow, ← mul_div_assoc, ← Finset.sum_div]
    ring
  rw [he]
  exact DRGPR.importance_second_bound _ _ _ _ (D.p_pos i) (D.q_pos i) (used_second D i)

theorem weighted_second [DecidableEq I] (D : Round I O) :
    D.avg (fun draw o => ∑ i, D.p i * (D.estimate draw o i)^2)
      ≤ D.d^2 * ∑ i, 1 / D.q i := by
  rw [avg_sum]
  simp_rw [avg_const_mul]
  calc
    (∑ i, D.p i * D.avg (fun draw o => (D.estimate draw o i)^2))
      ≤ ∑ i, D.p i * (D.d^2 / (D.p i * D.q i)) :=
      Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (estimate_second D i) (D.p_pos i).le
    _ = _ := DRGPR.weighted_second_cancel D.p D.q D.d D.p_pos D.q_pos

theorem learner_linear [DecidableEq I] (D : Round I O) :
    D.avg (fun draw o => ∑ i, D.p i * D.estimate draw o i)
      = D.avg (fun draw _ => D.loss draw) := by
  rw [avg_sum]
  simp_rw [avg_const_mul, estimate_mean]
  simp [avg, ← Finset.sum_mul, D.kernel_sum]

theorem comparator_linear [DecidableEq I] (D : Round I O) (v : I) :
    D.avg (fun draw o => D.estimate draw o v) = D.avg (fun _ _ => D.loss v) := by
  rw [estimate_mean]
  simp [avg, ← Finset.sum_mul, D.kernel_sum, D.p_sum]

theorem regret_linear [DecidableEq I] (D : Round I O) (v : I) :
    D.avg (fun draw o => (∑ i, D.p i * D.estimate draw o i) - D.estimate draw o v)
      = D.avg (fun draw _ => D.loss draw - D.loss v) := by
  rw [avg_sub, learner_linear, comparator_linear, ← avg_sub]

end Round
end DRGPR.FiniteObservation

#print axioms DRGPR.FiniteObservation.Round.estimate_mean
#print axioms DRGPR.FiniteObservation.Round.estimate_second
#print axioms DRGPR.FiniteObservation.Round.weighted_second
#print axioms DRGPR.FiniteObservation.Round.regret_linear
#print axioms DRGPR.FiniteObservation.Round.joint_nonneg
#print axioms DRGPR.FiniteObservation.Round.avg_one
#print axioms DRGPR.FiniteObservation.Round.avg_add
#print axioms DRGPR.FiniteObservation.Round.avg_sub
#print axioms DRGPR.FiniteObservation.Round.avg_const_mul
#print axioms DRGPR.FiniteObservation.Round.avg_sum
#print axioms DRGPR.FiniteObservation.Round.avg_mono
#print axioms DRGPR.FiniteObservation.Round.used_nonneg
#print axioms DRGPR.FiniteObservation.Round.used_le
#print axioms DRGPR.FiniteObservation.Round.estimate_nonneg
#print axioms DRGPR.FiniteObservation.Round.used_second
#print axioms DRGPR.FiniteObservation.Round.learner_linear
#print axioms DRGPR.FiniteObservation.Round.comparator_linear
