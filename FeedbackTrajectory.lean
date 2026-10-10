import LocalFeedbackStability

/-! Actual finite path probabilities underlying the local feedback theorem.
No equality between arbitrary native and reference costs is assumed. -/
noncomputable section
open scoped BigOperators
namespace DRGPR.FeedbackTrajectory
open LocalFeedbackStability
variable {I : ℕ → Type} [∀ t, Fintype (I t)]

def Trace (I : ℕ → Type) : ℕ → ℕ → Type
  | _, 0 => Unit
  | t, n+1 => I (t+1) × Trace I (t+1) n

instance traceFintype : (t n : ℕ) → Fintype (Trace I t n)
  | _, 0 => inferInstanceAs (Fintype Unit)
  | t, n+1 => by
    letI := traceFintype (t+1) n
    exact inferInstanceAs (Fintype (I (t+1) × Trace I (t+1) n))

def weight (K : Dynamics I) : (t n : ℕ) → I t → Trace I t n → ℝ
  | _, 0, _, _ => 1
  | t, n+1, s, h => (K t s).val h.1 * weight K (t+1) n h.1 h.2

def loss (c : (t : ℕ) → I t → ℝ) : (t n : ℕ) → I t → Trace I t n → ℝ
  | _, 0, _, _ => 0
  | t, n+1, s, h => c t s + loss c (t+1) n h.1 h.2

theorem normalized (K : Dynamics I) : ∀ t n s, ∑ h, weight K t n s h = 1 := by
  intro t n
  induction n generalizing t with
  | zero => intro s; simp [Trace,weight]
  | succ n ih =>
    intro s
    change (∑ h : I (t+1) × Trace I (t+1) n,
      (K t s).val h.1 * weight K (t+1) n h.1 h.2) = 1
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum,ih,mul_one]
    exact (K t s).sum_one

theorem nonneg (K : Dynamics I) : ∀ t n s h, 0 ≤ weight K t n s h := by
  intro t n
  induction n generalizing t with
  | zero => intro s h; exact zero_le_one
  | succ n ih => intro s h; exact mul_nonneg ((K t s).nonneg h.1) (ih _ _ _)

theorem expected_loss (K : Dynamics I) (c : (t : ℕ) → I t → ℝ) :
    ∀ t n s, (∑ h, weight K t n s h * loss c t n s h) = value K c t n s := by
  intro t n
  induction n generalizing t with
  | zero => intro s; simp [Trace,weight,loss,value]
  | succ n ih =>
    intro s
    change (∑ h : I (t+1) × Trace I (t+1) n,
      ((K t s).val h.1 * weight K (t+1) n h.1 h.2) *
        (c t s+loss c (t+1) n h.1 h.2)) = _
    rw [Fintype.sum_prod_type]
    have hs (j : I (t+1)) :
        (∑ h, ((K t s).val j * weight K (t+1) n j h) *
          (c t s+loss c (t+1) n j h)) =
          (K t s).val j*c t s + (K t s).val j*value K c (t+1) n j := by
      simp only [mul_add,Finset.sum_add_distrib,mul_assoc]
      rw [← Finset.mul_sum,← Finset.sum_mul,normalized,one_mul,
        ← Finset.mul_sum,ih]
    simp_rw [hs]
    rw [Finset.sum_add_distrib,← Finset.sum_mul,(K t s).sum_one,one_mul]
    rfl

def expected (K : Dynamics I) (c : (t : ℕ) → I t → ℝ)
    (p : FiniteController.Dist (I 0)) (T : ℕ) :=
  ∑ s, p.val s * ∑ h, weight K 0 T s h * loss c 0 T s h

theorem expected_eq_value (K : Dynamics I) (c : (t : ℕ) → I t → ℝ)
    (p : FiniteController.Dist (I 0)) (T : ℕ) :
    expected K c p T = DRGPR.mean p.val (value K c 0 T) := by
  simp only [expected,expected_loss,DRGPR.mean]

theorem local_to_actual_loss (K L : Dynamics I) (c : (t : ℕ) → I t → ℝ)
    (p : FiniteController.Dist (I 0)) (T : ℕ) (C : Contract K L c T) :
    |expected K c p T-expected L c p T| ≤ C.budget := by
  rw [expected_eq_value,expected_eq_value]
  exact initial_difference K L c T C p

end DRGPR.FeedbackTrajectory
#print axioms DRGPR.FeedbackTrajectory.normalized
#print axioms DRGPR.FeedbackTrajectory.nonneg
#print axioms DRGPR.FeedbackTrajectory.expected_loss
#print axioms DRGPR.FeedbackTrajectory.expected_eq_value
#print axioms DRGPR.FeedbackTrajectory.local_to_actual_loss
