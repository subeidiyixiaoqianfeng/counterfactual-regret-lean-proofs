import FiniteDynamics
import NativeNoRegret

/-! A local repair for feedback coarsening, without installing a controller.
K and L are complete behavior-state kernels, not just card-text marginals.
Their state types may change with time. The loss is the actual task score.
The continuation-range premise is explicit: local TV error alone does not
imply a sublinear accumulated loss error. -/
noncomputable section
open scoped BigOperators
namespace DRGPR.LocalFeedbackStability
open FiniteController FiniteTV

theorem span_test {J : Type} [Fintype J] (p q : FiniteController.Dist J) (f : J → ℝ)
    (a H : ℝ) (hH : 0 ≤ H) (hf : ∀ j, a ≤ f j ∧ f j ≤ a+H) :
    |DRGPR.mean p.val f - DRGPR.mean q.val f| ≤ H * tv p q := by
  have hz : (∑ j, (p.val j-q.val j)) = 0 := by
    rw [Finset.sum_sub_distrib,p.sum_one,q.sum_one]
    ring
  have he : 2*(DRGPR.mean p.val f-DRGPR.mean q.val f) =
      ∑ j, (p.val j-q.val j)*(2*f j-(2*a+H)) := by
    have hx (j : J) : (p.val j-q.val j)*(2*f j-(2*a+H)) =
        2*(p.val j*f j-q.val j*f j) - (p.val j-q.val j)*(2*a+H) := by ring
    simp_rw [hx]
    rw [Finset.sum_sub_distrib,← Finset.mul_sum,← Finset.sum_mul,hz,
      Finset.sum_sub_distrib]
    simp [DRGPR.mean]
  have hb (j : J) : |2*f j-(2*a+H)| ≤ H :=
    abs_le.mpr ⟨by linarith [(hf j).1], by linarith [(hf j).2]⟩
  have hh : |∑ j, (p.val j-q.val j)*(2*f j-(2*a+H))| ≤
      (∑ j, |p.val j-q.val j|)*H := by
    calc
      _ ≤ ∑ j, |(p.val j-q.val j)*(2*f j-(2*a+H))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, |p.val j-q.val j| * H := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hb j) (abs_nonneg _)
      _ = _ := (Finset.sum_mul _ _ _).symm
  rw [← he,abs_mul] at hh
  norm_num at hh
  unfold tv
  nlinarith

variable {I : ℕ → Type} [∀ t, Fintype (I t)]

/-- Each kernel takes the full sufficient state. Variable finite types allow
growing registries in a finite-horizon representation. -/
abbrev Dynamics (I : ℕ → Type) [∀ t, Fintype (I t)] :=
  (t : ℕ) → I t → FiniteController.Dist (I (t+1))

def value (K : Dynamics I) (c : (t : ℕ) → I t → ℝ) :
    (t n : ℕ) → I t → ℝ
  | _, 0, _ => 0
  | t, n+1, s => c t s + DRGPR.mean (K t s).val (value K c (t+1) n)

def charge (w : ℕ → ℝ) : ℕ → ℕ → ℝ
  | _, 0 => 0
  | t, n+1 => w t + charge w (t+1) n

theorem charge_nonneg (w : ℕ → ℝ) (hw : ∀ t, 0 ≤ w t) :
    ∀ t n, 0 ≤ charge w t n := by
  intro t n
  induction n generalizing t with
  | zero => exact le_rfl
  | succ n ih => exact add_nonneg (hw t) (ih (t+1))

theorem charge_mono (w z : ℕ → ℝ) (h : ∀ t, w t ≤ z t) :
    ∀ t n, charge w t n ≤ charge z t n := by
  intro t n
  induction n generalizing t with
  | zero => exact le_rfl
  | succ n ih => exact add_le_add (h t) (ih (t+1))

theorem charge_const_mul (a : ℝ) (w : ℕ → ℝ) :
    ∀ t n, charge (fun r => a*w r) t n = a*charge w t n := by
  intro t n
  induction n generalizing t with
  | zero => simp [charge]
  | succ n ih => simp only [charge,ih]; ring

/-- A local model contract, not a regret inequality. The range requirement
is only imposed at transitions whose coarsening error is nonzero. Without
such a condition or vanishing errors, the bound may be linear or worse. -/
structure Contract (K L : Dynamics I) (c : (t : ℕ) → I t → ℝ) (T : ℕ) where
  epsilon : ℕ → ℝ
  influence : ℕ → ℝ
  epsilon_nonneg : ∀ t, 0 ≤ epsilon t
  influence_nonneg : ∀ t, 0 ≤ influence t
  local_tv : ∀ t, t < T → ∀ s, tv (K t s) (L t s) ≤ epsilon t
  lower : (t n : ℕ) → ℝ
  continuation : ∀ t n, t+n+1 ≤ T → epsilon t ≠ 0 →
    ∀ s, lower t n ≤ value L c (t+1) n s ∧
      value L c (t+1) n s ≤ lower t n + influence t

def Contract.budget {K L : Dynamics I} {c : (t : ℕ) → I t → ℝ} {T : ℕ}
    (C : Contract K L c T) :=
  charge (fun t => C.influence t*C.epsilon t) 0 T

theorem value_difference (K L : Dynamics I) (c : (t : ℕ) → I t → ℝ)
    (T : ℕ) (C : Contract K L c T) :
    ∀ t n, t+n ≤ T → ∀ s,
      |value K c t n s-value L c t n s| ≤
        charge (fun r => C.influence r*C.epsilon r) t n := by
  intro t n
  induction n generalizing t with
  | zero => intro _ s; simp [value,charge]
  | succ n ih =>
    intro htn s
    have ht : t < T := by omega
    have hnext : (t+1)+n ≤ T := by omega
    let u := value K c (t+1) n
    let v := value L c (t+1) n
    let b := charge (fun r => C.influence r*C.epsilon r) (t+1) n
    have hp : |DRGPR.mean (K t s).val u-DRGPR.mean (K t s).val v| ≤ b := by
      rw [← DRGPR.mean_sub]
      calc
        _ ≤ ∑ j, |(K t s).val j*(u j-v j)| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ j, (K t s).val j*|u j-v j| := by
          simp_rw [abs_mul,abs_of_nonneg ((K t s).nonneg _)]
        _ ≤ ∑ j, (K t s).val j*b :=
          Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left
            (ih (t+1) hnext j) ((K t s).nonneg j))
        _ = b := by rw [← Finset.sum_mul,(K t s).sum_one,one_mul]
    have hl : |DRGPR.mean (K t s).val v-DRGPR.mean (L t s).val v| ≤
        C.influence t*C.epsilon t := by
      by_cases he : C.epsilon t = 0
      · have ht0 : tv (K t s) (L t s) = 0 :=
          le_antisymm (by simpa [he] using C.local_tv t ht s) (FiniteTV.nonneg _ _)
        have hsame : (K t s).val = (L t s).val := by
          funext j
          have hsum : (∑ j, |(K t s).val j-(L t s).val j|) = 0 := by
            unfold tv at ht0
            linarith
          have hx := Finset.single_le_sum (fun k _ => abs_nonneg ((K t s).val k-(L t s).val k))
            (Finset.mem_univ j)
          rw [hsum] at hx
          exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hx (abs_nonneg _)))
        simp [hsame,he]
      · exact (span_test (K t s) (L t s) v (C.lower t n) (C.influence t)
          (C.influence_nonneg t) (C.continuation t n (by omega) he)).trans
          (mul_le_mul_of_nonneg_left (C.local_tv t ht s) (C.influence_nonneg t))
    have htri := abs_sub_le (DRGPR.mean (K t s).val u)
      (DRGPR.mean (K t s).val v) (DRGPR.mean (L t s).val v)
    change |(c t s+DRGPR.mean (K t s).val u)-
      (c t s+DRGPR.mean (L t s).val v)| ≤ C.influence t*C.epsilon t+b
    rw [add_sub_add_left_eq_sub]
    linarith

theorem initial_difference (K L : Dynamics I) (c : (t : ℕ) → I t → ℝ)
    (T : ℕ) (C : Contract K L c T) (p : FiniteController.Dist (I 0)) :
    |DRGPR.mean p.val (value K c 0 T)-DRGPR.mean p.val (value L c 0 T)| ≤ C.budget := by
  rw [← DRGPR.mean_sub]
  calc
    _ ≤ ∑ s, |p.val s*(value K c 0 T s-value L c 0 T s)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ s, p.val s*|value K c 0 T s-value L c 0 T s| := by
      simp_rw [abs_mul,abs_of_nonneg (p.nonneg _)]
    _ ≤ ∑ s, p.val s*C.budget := Finset.sum_le_sum
      (fun s _ => mul_le_mul_of_nonneg_left (value_difference K L c T C 0 T (by omega) s) (p.nonneg s))
    _ = _ := by rw [← Finset.sum_mul,p.sum_one,one_mul]

end DRGPR.LocalFeedbackStability
#print axioms DRGPR.LocalFeedbackStability.span_test
#print axioms DRGPR.LocalFeedbackStability.charge_nonneg
#print axioms DRGPR.LocalFeedbackStability.charge_mono
#print axioms DRGPR.LocalFeedbackStability.charge_const_mul
#print axioms DRGPR.LocalFeedbackStability.value_difference
#print axioms DRGPR.LocalFeedbackStability.initial_difference
