import FeedbackRepairMain

/-! The least structural repair: bounded task losses plus local TV control.
No contraction, memory reset, bounded card lifetime, or external controller
is imposed. The price is a horizon-dependent perturbation bound. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace DRGPR.FeedbackLocalOnly
open LocalFeedbackStability FeedbackTrajectory
variable {I : ℕ → Type} [∀ t, Fintype (I t)]

theorem value_bounds (K : Dynamics I) (c : (t : ℕ) → I t → ℝ)
    (hc : ∀ t s, 0 ≤ c t s ∧ c t s ≤ 1) :
    ∀ t n s, 0 ≤ value K c t n s ∧ value K c t n s ≤ (n:ℝ) := by
  intro t n
  induction n generalizing t with
  | zero => intro s; simp [value]
  | succ n ih =>
    intro s
    have h0 : 0 ≤ DRGPR.mean (K t s).val (value K c (t+1) n) :=
      Finset.sum_nonneg (fun j _ => mul_nonneg ((K t s).nonneg j) (ih (t+1) j).1)
    have h1 : DRGPR.mean (K t s).val (value K c (t+1) n) ≤ (n:ℝ) := by
      calc
        _ ≤ DRGPR.mean (K t s).val (fun _ => (n:ℝ)) :=
          DRGPR.mean_mono _ _ _ (K t s).nonneg (fun j => (ih (t+1) j).2)
        _ = _ := DRGPR.mean_const _ (K t s).sum_one _
    constructor
    · exact add_nonneg (hc t s).1 h0
    · change c t s+DRGPR.mean (K t s).val (value K c (t+1) n) ≤ ((n+1:ℕ):ℝ)
      push_cast
      linarith [(hc t s).2]

def localContract (K L : Dynamics I) (c : (t : ℕ) → I t → ℝ) (T : ℕ)
    (hc : ∀ t s, 0 ≤ c t s ∧ c t s ≤ 1)
    (eps : ℕ → ℝ) (heps : ∀ t, 0 ≤ eps t)
    (hlocal : ∀ t, t < T → ∀ s, FiniteTV.tv (K t s) (L t s) ≤ eps t) :
    Contract K L c T where
  epsilon := eps
  influence t := (T-t-1:ℕ)
  epsilon_nonneg := heps
  influence_nonneg t := Nat.cast_nonneg _
  local_tv := hlocal
  lower _ _ := 0
  continuation t n htn _ s := by
    have hb := value_bounds L c hc (t+1) n s
    constructor
    · exact hb.1
    · have hn : n ≤ T-t-1 := by omega
      have hn' : (n:ℝ) ≤ ((T-t-1:ℕ):ℝ) := by exact_mod_cast hn
      simpa using hb.2.trans hn'

theorem local_only_loss (K L : Dynamics I) (c : (t : ℕ) → I t → ℝ)
    (p : FiniteController.Dist (I 0)) (T : ℕ)
    (hc : ∀ t s, 0 ≤ c t s ∧ c t s ≤ 1)
    (eps : ℕ → ℝ) (heps : ∀ t, 0 ≤ eps t)
    (hlocal : ∀ t, t < T → ∀ s, FiniteTV.tv (K t s) (L t s) ≤ eps t) :
    |expected K c p T-expected L c p T| ≤
      charge (fun t => ((T-t-1:ℕ):ℝ)*eps t) 0 T :=
  local_to_actual_loss K L c p T (localContract K L c T hc eps heps hlocal)

theorem charge_constant (a : ℝ) : ∀ t n, charge (fun _ => a) t n = (n:ℝ)*a := by
  intro t n
  induction n generalizing t with
  | zero => simp [charge]
  | succ n ih => simp only [charge,ih,Nat.cast_add,Nat.cast_one]; ring

/-- A conservative T-squared bound follows from the local hypothesis alone.
It is sublinear when T*epsilon_T tends to zero, not for fixed epsilon. -/
theorem uniform_local_bound (K L : Dynamics I) (c : (t : ℕ) → I t → ℝ)
    (p : FiniteController.Dist (I 0)) (T : ℕ)
    (hc : ∀ t s, 0 ≤ c t s ∧ c t s ≤ 1) (eps : ℝ) (heps : 0 ≤ eps)
    (hlocal : ∀ t, t < T → ∀ s, FiniteTV.tv (K t s) (L t s) ≤ eps) :
    |expected K c p T-expected L c p T| ≤ (T:ℝ)^2*eps := by
  apply (local_only_loss K L c p T hc (fun _ => eps) (fun _ => heps) hlocal).trans
  have hm : ∀ t, ((T-t-1:ℕ):ℝ)*eps ≤ (T:ℝ)*eps := by
    intro t
    apply mul_le_mul_of_nonneg_right _ heps
    exact_mod_cast (show T-t-1 ≤ T by omega)
  have hh := charge_mono _ _ hm 0 T
  rw [charge_constant] at hh
  convert hh using 1 <;> ring

theorem local_only_rate (T eps : ℕ → ℝ)
    (hT : ∀ n, T n ≠ 0)
    (he : Tendsto (fun n => T n*eps n) atTop (𝓝 0)) :
    Tendsto (fun n => ((T n)^2*eps n)/T n) atTop (𝓝 0) := by
  have hx : ∀ n, ((T n)^2*eps n)/T n = T n*eps n := by
    intro n
    field_simp [hT n]
    ring
  simpa only [hx] using he

end DRGPR.FeedbackLocalOnly
#print axioms DRGPR.FeedbackLocalOnly.value_bounds
#print axioms DRGPR.FeedbackLocalOnly.local_only_loss
#print axioms DRGPR.FeedbackLocalOnly.charge_constant
#print axioms DRGPR.FeedbackLocalOnly.uniform_local_bound
#print axioms DRGPR.FeedbackLocalOnly.local_only_rate
