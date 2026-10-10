import FiniteObservation
import GrowingPotential

/-! Finite stochastic lifting of the recursively defined growing potential.
The input is an atomic joint-law contract on a common finite sample space.
No expected selection-regret inequality is assumed. The module does not
construct a general Borel-space agent, its runtime, or the lower-bound adversary.
Eligible identity TYPES vary with time but not with the sample point. -/
noncomputable section
open scoped BigOperators
namespace DRGPR.FiniteStochastic

theorem mean_add {Ω : Type*} [Fintype Ω] (m f g : Ω → ℝ) :
    DRGPR.mean m (fun ω => f ω + g ω) = DRGPR.mean m f + DRGPR.mean m g := by
  simp [DRGPR.mean, mul_add, Finset.sum_add_distrib]

theorem mean_mul {Ω : Type*} [Fintype Ω] (m f : Ω → ℝ) (a : ℝ) :
    DRGPR.mean m (fun ω => a*f ω) = a*DRGPR.mean m f := by
  simp only [DRGPR.mean, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  ring

theorem mean_range {Ω : Type*} [Fintype Ω] (m : Ω → ℝ) (f : ℕ → Ω → ℝ) (n : ℕ) :
    DRGPR.mean m (fun ω => ∑ r ∈ Finset.range n, f r ω)
      = ∑ r ∈ Finset.range n, DRGPR.mean m (f r) := by
  induction n with
  | zero => simp [DRGPR.mean]
  | succ n ih => simp only [Finset.sum_range_succ, mean_add, ih]

theorem pushforward_mean {Ω X : Type*} [Fintype Ω] [Fintype X] [DecidableEq X]
    (m : Ω → ℝ) (s : Ω → X) (π : X → ℝ)
    (law : ∀ x, (∑ ω, if s ω = x then m ω else 0) = π x) (f : X → ℝ) :
    DRGPR.mean m (fun ω => f (s ω)) = DRGPR.mean π f := by
  classical
  unfold DRGPR.mean
  calc
    (∑ ω, m ω*f (s ω)) = ∑ ω, ∑ x, (if s ω = x then m ω else 0)*f x := by
      apply Finset.sum_congr rfl
      intro ω _
      simp [ite_mul]
    _ = ∑ x, ∑ ω, (if s ω = x then m ω else 0)*f x := by rw [Finset.sum_comm]
    _ = ∑ x, (∑ ω, if s ω = x then m ω else 0)*f x := by simp [Finset.sum_mul]
    _ = ∑ x, π x*f x := by simp_rw [law]

structure Realization (Ω I H O : Type*) [Fintype Ω] [Fintype I] [Fintype H] [Fintype O]
    [DecidableEq I] [DecidableEq H] [DecidableEq O] (m : Ω → ℝ) where
  model : H → DRGPR.FiniteObservation.Round I O
  historyMass : H → ℝ
  historyMass_nonneg : ∀ h, 0 ≤ historyMass h
  sample : Ω → H × I × O
  law : ∀ s : H × I × O,
    (∑ ω, if sample ω = s then m ω else 0) =
      historyMass s.1 * (model s.1).p s.2.1 * (model s.1).kernel s.2.1 s.2.2

namespace Realization
variable {Ω I H O : Type*} [Fintype Ω] [Fintype I] [Fintype H] [Fintype O]
  [DecidableEq I] [DecidableEq H] [DecidableEq O] {m : Ω → ℝ}

def prob (X : Realization Ω I H O m) (ω : Ω) : I → ℝ := (X.model (X.sample ω).1).p
def est (X : Realization Ω I H O m) (ω : Ω) (i : I) : ℝ :=
  (X.model (X.sample ω).1).estimate (X.sample ω).2.1 (X.sample ω).2.2 i
def selectedLoss (X : Realization Ω I H O m) (ω : Ω) : ℝ :=
  (X.model (X.sample ω).1).loss (X.sample ω).2.1
def bridgeLoss (X : Realization Ω I H O m) (v : H → I) (ω : Ω) : ℝ :=
  (X.model (X.sample ω).1).loss (v (X.sample ω).1)
def activity (X : Realization Ω I H O m) : ℝ :=
  ∑ h, X.historyMass h * ((X.model h).d * ∑ i, 1/(X.model h).q i)

theorem integral (X : Realization Ω I H O m) (f : H × I × O → ℝ) :
    DRGPR.mean m (fun ω => f (X.sample ω)) =
      ∑ h, X.historyMass h * (X.model h).avg (fun i o => f (h,i,o)) := by
  rw [pushforward_mean m X.sample _ X.law f]
  simp only [DRGPR.mean, Fintype.sum_prod_type, DRGPR.FiniteObservation.Round.avg,
    Finset.mul_sum, mul_assoc]

theorem linear (X : Realization Ω I H O m) (v : H → I) :
    DRGPR.mean m (fun ω => DRGPR.mean (X.prob ω) (X.est ω) - X.est ω (v (X.sample ω).1)) =
      DRGPR.mean m (fun ω => X.selectedLoss ω - X.bridgeLoss v ω) := by
  change DRGPR.mean m (fun ω =>
    (∑ i, (X.model (X.sample ω).1).p i *
      (X.model (X.sample ω).1).estimate (X.sample ω).2.1 (X.sample ω).2.2 i) -
      (X.model (X.sample ω).1).estimate (X.sample ω).2.1 (X.sample ω).2.2 (v (X.sample ω).1)) = _
  unfold selectedLoss bridgeLoss
  rw [X.integral (fun s => (∑ i, (X.model s.1).p i *
      (X.model s.1).estimate s.2.1 s.2.2 i) -
      (X.model s.1).estimate s.2.1 s.2.2 (v s.1)),
    X.integral (fun s => (X.model s.1).loss s.2.1 - (X.model s.1).loss (v s.1))]
  apply Finset.sum_congr rfl
  intro h _
  exact congrArg (fun t : ℝ => X.historyMass h * t)
    (DRGPR.FiniteObservation.Round.regret_linear (X.model h) (v h))

theorem quadratic (X : Realization Ω I H O m) (b : ℝ) (hb : 0 ≤ b)
    (cap : ∀ h, (X.model h).d ≤ b) :
    DRGPR.mean m (fun ω => DRGPR.mean (X.prob ω) (fun i => (X.est ω i)^2)) ≤ b*X.activity := by
  change DRGPR.mean m (fun ω => ∑ i, (X.model (X.sample ω).1).p i *
    ((X.model (X.sample ω).1).estimate (X.sample ω).2.1 (X.sample ω).2.2 i)^2) ≤ _
  rw [X.integral (fun s => ∑ i, (X.model s.1).p i *
    ((X.model s.1).estimate s.2.1 s.2.2 i)^2)]
  unfold activity
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro h _
  have hk : 0 ≤ ∑ i, 1/(X.model h).q i :=
    Finset.sum_nonneg fun i _ => (div_pos (by norm_num) ((X.model h).q_pos i)).le
  have hs := DRGPR.FiniteObservation.Round.weighted_second (X.model h)
  have hd := mul_le_mul_of_nonneg_right
    (DRGPR.capped_square (X.model h).d b (X.model h).d_nonneg (cap h)) hk
  have ht := mul_le_mul_of_nonneg_left (le_trans hs hd) (X.historyMass_nonneg h)
  simpa only [mul_assoc, mul_left_comm] using ht

end Realization

variable {Ω H O : Type*} [Fintype Ω] [Fintype H] [Fintype O]
  [DecidableEq H] [DecidableEq O]
  {ι : ℕ → Type*} [∀ r, Fintype (ι r)] [∀ r, DecidableEq (ι r)]

theorem expected_growing_selection
    (m : Ω → ℝ) (hm : ∀ ω, 0 ≤ m ω) (hm1 : ∑ ω, m ω = 1)
    (X : ∀ r, Realization Ω (ι r) H O m)
    (ν : Ω → ι 0 → ℝ) (P : ∀ ω r, ι r → ι (r+1) → ℝ)
    (z : ∀ ω r, ι r → ℝ) (η b C V : ℝ) (R : ℕ)
    (v : ∀ r, H → ι r)
    (hη : 0 < η) (hb : 0 ≤ b)
    (hν : ∀ ω i, 0 ≤ ν ω i) (hν1 : ∀ ω, ∑ i, ν ω i = 1)
    (hP : ∀ ω r i j, 0 ≤ P ω r i j)
    (hP1 : ∀ ω r i, ∑ j, P ω r i j = 1)
    (hp : ∀ ω r i, DRGPR.Growing.prob (ν ω) (P ω) (z ω) η r i = (X r).prob ω i)
    (hz : ∀ ω r i, z ω r i = (X r).est ω i)
    (hv0 : ∀ ω, 0 < ν ω (v 0 ((X 0).sample ω).1))
    (hvP : ∀ ω r, 0 < P ω r (v r ((X r).sample ω).1)
      (v (r+1) ((X (r+1)).sample ω).1))
    (hcode : ∀ ω, -(Real.log (ν ω (v 0 ((X 0).sample ω).1)) +
      ∑ r ∈ Finset.range R, Real.log (P ω r (v r ((X r).sample ω).1)
        (v (r+1) ((X (r+1)).sample ω).1))) ≤ C)
    (cap : ∀ r h, ((X r).model h).d ≤ b)
    (capacity : (∑ r ∈ Finset.range (R+1), (X r).activity) ≤ V) :
    (∑ r ∈ Finset.range (R+1), DRGPR.mean m (fun ω =>
      (X r).selectedLoss ω - (X r).bridgeLoss (v r) ω)) ≤ C/η + η*b*V/2 := by
  classical
  let path : ∀ ω r, ι r := fun ω r => v r ((X r).sample ω).1
  have hz0 : ∀ ω r i, 0 ≤ z ω r i := by
    intro ω r i
    rw [hz]
    exact DRGPR.FiniteObservation.Round.estimate_nonneg _ _ _ _
  have hpoint (ω : Ω) :
      (∑ r ∈ Finset.range (R+1), DRGPR.mean (DRGPR.Growing.prob (ν ω) (P ω) (z ω) η r) (z ω r)) -
      (∑ r ∈ Finset.range (R+1), z ω r (path ω r)) ≤ C/η + η/2 *
      (∑ r ∈ Finset.range (R+1), DRGPR.mean (DRGPR.Growing.prob (ν ω) (P ω) (z ω) η r)
        (fun i => (z ω r i)^2)) := by
    have hpot := DRGPR.Growing.growing_path_regret (ν ω) (P ω) (z ω) η
      (hν ω) (hν1 ω) (hP ω) (hP1 ω) hη (hz0 ω) (path ω) (hv0 ω) (hvP ω) R
    exact le_trans hpot (add_le_add_right
      (div_le_div_of_nonneg_right (hcode ω) hη.le) _)
  have havg := DRGPR.mean_mono m _ _ hm hpoint
  have hlin (r : ℕ) :
      DRGPR.mean m (fun ω => DRGPR.mean (DRGPR.Growing.prob (ν ω) (P ω) (z ω) η r) (z ω r) -
        z ω r (path ω r)) = DRGPR.mean m (fun ω =>
        (X r).selectedLoss ω - (X r).bridgeLoss (v r) ω) := by
    simp only [DRGPR.mean, hp, hz, path]
    exact (X r).linear (v r)
  have hvar : DRGPR.mean m (fun ω =>
      ∑ r ∈ Finset.range (R+1), DRGPR.mean (DRGPR.Growing.prob (ν ω) (P ω) (z ω) η r)
        (fun i => (z ω r i)^2)) ≤ b*V := by
    rw [mean_range]
    calc
      _ ≤ ∑ r ∈ Finset.range (R+1), b*(X r).activity := by
        apply Finset.sum_le_sum
        intro r _
        simp only [DRGPR.mean, hp, hz]
        exact (X r).quadratic b hb (cap r)
      _ = b*(∑ r ∈ Finset.range (R+1), (X r).activity) := by rw [Finset.mul_sum]
      _ ≤ b*V := mul_le_mul_of_nonneg_left capacity hb
  simp_rw [← Finset.sum_sub_distrib] at havg
  rw [mean_range] at havg
  simp_rw [hlin] at havg
  rw [mean_add, DRGPR.mean_const m hm1, mean_mul] at havg
  have := mul_le_mul_of_nonneg_left hvar (by positivity : 0 ≤ η/2)
  nlinarith

end DRGPR.FiniteStochastic

#print axioms DRGPR.FiniteStochastic.pushforward_mean
#print axioms DRGPR.FiniteStochastic.Realization.integral
#print axioms DRGPR.FiniteStochastic.Realization.linear
#print axioms DRGPR.FiniteStochastic.Realization.quadratic
#print axioms DRGPR.FiniteStochastic.expected_growing_selection
#print axioms DRGPR.FiniteStochastic.mean_add
#print axioms DRGPR.FiniteStochastic.mean_mul
#print axioms DRGPR.FiniteStochastic.mean_range
