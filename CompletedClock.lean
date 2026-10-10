import LocalNativeFamily

noncomputable section
open scoped BigOperators
namespace DRGPR.CompletedClock
open LocalFeedbackStability FeedbackTrajectory
variable {X : ℕ → Type} [∀ t, Fintype (X t)]

/-- A completed task is scored at its destination state. The state may be
the complete finite history, so this does not assume memoryless scoring. -/
def postValue (K : Dynamics X) (c : (t : ℕ) → X (t+1) → ℝ) :
    (t n : ℕ) → X t → ℝ
  | _, 0, _ => 0
  | t, n+1, s => DRGPR.mean (K t s).val
      (fun j => c t j + postValue K c (t+1) n j)

def padded (c : (t : ℕ) → X (t+1) → ℝ) : (t : ℕ) → X t → ℝ
  | 0, _ => 0
  | t+1, s => c t s

def postLoss (c : (t : ℕ) → X (t+1) → ℝ) :
    (t n : ℕ) → X t → Trace X t n → ℝ
  | _, 0, _, _ => 0
  | t, n+1, _, h => c t h.1 + postLoss c (t+1) n h.1 h.2

theorem post_trace_value (K : Dynamics X) (c : (t : ℕ) → X (t+1) → ℝ) :
    ∀ t n s, (∑ h, weight K t n s h * postLoss c t n s h) = postValue K c t n s := by
  intro t n
  induction n generalizing t with
  | zero => intro s; simp [Trace, weight, postLoss, postValue]
  | succ n ih =>
    intro s
    change (∑ h : X (t+1) × Trace X (t+1) n,
      ((K t s).val h.1 * weight K (t+1) n h.1 h.2) *
        (c t h.1 + postLoss c (t+1) n h.1 h.2)) = _
    rw [Fintype.sum_prod_type]
    unfold postValue DRGPR.mean
    apply Finset.sum_congr rfl
    intro j _
    simp only [mul_add, Finset.sum_add_distrib, mul_assoc]
    rw [← Finset.mul_sum, ← Finset.sum_mul, normalized, one_mul,
      ← Finset.mul_sum, ih]

theorem shifted_value (K : Dynamics X) (c : (t : ℕ) → X (t+1) → ℝ) :
    ∀ t n s, value K (padded c) (t+1) (n+1) s = c t s + postValue K c (t+1) n s := by
  intro t n
  induction n generalizing t with
  | zero => intro s; simp [value, padded, postValue, DRGPR.mean]
  | succ n ih =>
    intro s
    change c t s + DRGPR.mean (K (t+1) s).val (value K (padded c) (t+1+1) (n+1)) =
      c t s + DRGPR.mean (K (t+1) s).val (fun j => c (t+1) j + postValue K c (t+1+1) n j)
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [ih]

def completedExpected (K : Dynamics X) (c : (t : ℕ) → X (t+1) → ℝ)
    (p : FiniteController.Dist (X 0)) (T : ℕ) : ℝ :=
  ∑ s, p.val s * ∑ h, weight K 0 T s h * postLoss c 0 T s h

theorem completed_clock (K : Dynamics X) (c : (t : ℕ) → X (t+1) → ℝ)
    (p : FiniteController.Dist (X 0)) (T : ℕ) :
    completedExpected K c p T = expected K (padded c) p (T+1) := by
  simp only [completedExpected, post_trace_value, expected_eq_value]
  apply Finset.sum_congr rfl
  intro s _
  congr 1
  cases T with
  | zero => simp [postValue, value, padded, DRGPR.mean]
  | succ n =>
    change DRGPR.mean (K 0 s).val (fun j => c 0 j + postValue K c 1 n j) =
      0 + DRGPR.mean (K 0 s).val (value K (padded c) 1 (n+1))
    rw [zero_add (DRGPR.mean (K 0 s).val (value K (padded c) 1 (n+1)))]
    apply Finset.sum_congr rfl
    intro j _
    rw [shifted_value]

/-- The extra state-score position is not an extra task. Both end scores
are retained. No equality of the first completed score laws is assumed. -/
theorem completed_local_gap (K L : Dynamics X)
    (c : (t : ℕ) → X (t+1) → ℝ) (p : FiniteController.Dist (X 0)) (T : ℕ)
    (H eps cmin B : ℝ) (hH : 0 ≤ H) (he : 0 ≤ eps) (hc : 0 < cmin)
    (D : NativeRepairEndpoint.Side K L (padded c) p (T+1) H eps cmin B) :
    |completedExpected K c p T-completedExpected L c p T| ≤ H*eps*B/cmin := by
  rw [completed_clock, completed_clock]
  exact D.gap K L (padded c) p (T+1) H eps cmin B hH he hc

theorem no_resource_no_error (tv epsilon activity resource eps cmin : ℝ)
    (htv : 0 ≤ tv) (hlocal : tv ≤ epsilon) (he : epsilon ≤ eps*activity)
    (ha : 0 ≤ activity) (hp : 0 < cmin) (hr : cmin*activity ≤ resource)
    (hz : resource = 0) : tv = 0 := by
  have haz : activity = 0 := by nlinarith
  rw [haz, mul_zero] at he
  linarith

theorem completed_local_only (K L : Dynamics X)
    (c : (t : ℕ) → X (t+1) → ℝ) (p : FiniteController.Dist (X 0)) (T : ℕ)
    (hc : ∀ t s, 0 ≤ c t s ∧ c t s ≤ 1) (eps : ℝ) (heps : 0 ≤ eps)
    (hl : ∀ t, t < T+1 → ∀ s, FiniteTV.tv (K t s) (L t s) ≤ eps) :
    |completedExpected K c p T-completedExpected L c p T| ≤ ((T:ℝ)+1)^2*eps := by
  rw [completed_clock, completed_clock]
  have hp : ∀ t s, 0 ≤ padded c t s ∧ padded c t s ≤ 1 := by
    intro t s
    cases t with
    | zero => simp [padded]
    | succ n => exact hc n s
  simpa using FeedbackLocalOnly.uniform_local_bound K L (padded c) p (T+1) hp eps heps hl

theorem accumulated_tv {F : Type} [Fintype F]
    (tv activity resource : F → ℝ) (eps cmin B : ℝ)
    (he : 0 ≤ eps) (hc : 0 < cmin)
    (hl : ∀ t, tv t ≤ eps*activity t)
    (hr : ∀ t, cmin*activity t ≤ resource t) (hb : ∑ t, resource t ≤ B) :
    (∑ t, tv t) ≤ eps*B/cmin := by
  have h1 := Finset.sum_le_sum (fun t (_ : t ∈ (Finset.univ : Finset F)) => hl t)
  have h2 := Finset.sum_le_sum (fun t (_ : t ∈ (Finset.univ : Finset F)) => hr t)
  simp only [← Finset.mul_sum] at h1 h2
  apply (le_div_iff₀ hc).mpr
  nlinarith

theorem sparse_normalized (q T a : ℝ) (hq : 0 < q) (hT : 0 < T)
    (hs : q^3*T ≤ a) : q^2 ≤ a/(q*T) := by
  apply (le_div_iff₀ (mul_pos hq hT)).mpr
  nlinarith

theorem adjacent_not_causal (a b c : ℝ) : a-c = (a-b)+(b-c) := by ring

theorem sparse_probability_limit (q a T : ℕ → ℝ)
    (hq : ∀ n, 0 < q n) (hT : ∀ n, 0 < T n)
    (hs : ∀ n, (q n)^3*T n ≤ a n)
    (hl : Filter.Tendsto (fun n => a n/(q n*T n)) Filter.atTop (nhds 0)) :
    Filter.Tendsto q Filter.atTop (nhds 0) := by
  have hb : ∀ n, q n ≤ Real.sqrt (a n/(q n*T n)) := by
    intro n
    have h := sparse_normalized (q n) (T n) (a n) (hq n) (hT n) (hs n)
    have hx := Real.sqrt_le_sqrt h
    simpa [Real.sqrt_sq (hq n).le] using hx
  apply squeeze_zero (fun n => (hq n).le) hb
  simpa using hl.sqrt

theorem persistent_tv_requires_resources (tv B eps cmin delta count : ℝ)
    (he : 0 < eps) (hc : 0 < cmin)
    (hl : delta*count ≤ tv) (hu : tv ≤ eps*B/cmin) :
    cmin*delta*count/eps ≤ B := by
  have ht := (le_div_iff₀ hc).mp hu
  apply (div_le_iff₀ he).mpr
  nlinarith

end DRGPR.CompletedClock
#print axioms DRGPR.CompletedClock.post_trace_value
#print axioms DRGPR.CompletedClock.shifted_value
#print axioms DRGPR.CompletedClock.completed_clock
#print axioms DRGPR.CompletedClock.completed_local_gap
#print axioms DRGPR.CompletedClock.no_resource_no_error
#print axioms DRGPR.CompletedClock.completed_local_only
#print axioms DRGPR.CompletedClock.accumulated_tv
#print axioms DRGPR.CompletedClock.sparse_normalized
#print axioms DRGPR.CompletedClock.adjacent_not_causal
#print axioms DRGPR.CompletedClock.sparse_probability_limit
#print axioms DRGPR.CompletedClock.persistent_tv_requires_resources
