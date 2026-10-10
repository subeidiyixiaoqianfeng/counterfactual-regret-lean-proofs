import PhaseSwitching

noncomputable section
open scoped BigOperators
namespace DRGPR.TunedPhase
open FiniteController PhaseAlgorithm PhaseSwitching PhaseTuning SupportedInformation
variable {I : Type} [Fintype I] [DecidableEq I]

theorem entropy_scale_ge_one (K : ℝ) (hK : 2 ≤ K) : 1 ≤ K*Real.log K := by
  have hk : 0 < K := by linarith
  have h := mul_le_mul_of_nonneg_left (Real.one_sub_inv_le_log_of_pos hk) hk.le
  rw [mul_sub,mul_one,mul_inv_cancel₀ hk.ne'] at h
  linarith

def rate (a V : ℝ) : ℝ := Real.sqrt (2*a/V)

theorem rate_pos (a V : ℝ) (ha : 0 < a) (hV : 0 < V) : 0 < rate a V := by
  exact Real.sqrt_pos.mpr (by positivity)

theorem tuned_identity (a V : ℝ) (ha : 0 < a) (hV : 0 < V) :
    a/rate a V+rate a V/2*V=Real.sqrt (2*a*V) := by
  let e := rate a V
  have he : 0 < e := rate_pos a V ha hV
  have hs : e^2=2*a/V := Real.sq_sqrt (by positivity)
  have hm : e^2*V=2*a := (eq_div_iff hV.ne').mp hs
  have hcancel : a/e=e*V/2 := (div_eq_iff he.ne').mpr (by nlinarith)
  change a/e+e/2*V=_
  rw [hcancel]
  have hsq : (e*V)^2=2*a*V := by nlinarith [congrArg (fun z : ℝ => z*V) hm]
  have hr := Real.sq_sqrt (show 0 ≤ 2*a*V by positivity)
  have hn := Real.sqrt_nonneg (2*a*V)
  have hp : 0 < e*V := mul_pos he hV
  nlinarith

theorem sqrt_sum_bound (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x+y) ≤ Real.sqrt x+Real.sqrt y := by
  apply (Real.sqrt_le_left (by positivity)).mpr
  nlinarith [Real.sq_sqrt hx,Real.sq_sqrt hy,
    mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)]

def runCap (T : ℕ) (K : ℝ) : ℕ := cap T (((T:ℝ)/(K*Real.log K))^((1:ℝ)/3))

theorem runCap_pos (T : ℕ) (K : ℝ) (hT : 0 < T) : 0 < runCap T K := by
  exact lt_min hT (lt_of_lt_of_le (by decide : 0 < (1:ℕ)) (le_max_left _ _))

def varianceBudget (T b : ℕ) (K q : ℝ) : ℝ := K*((b:ℝ)+1/q)*T

theorem varianceBudget_pos (T b : ℕ) (K q : ℝ) (hT : 0 < T) (hK : 0 < K) (hq : 0 < q) :
    0 < varianceBudget T b K q := by
  unfold varianceBudget
  have ht : (0:ℝ) < T := Nat.cast_pos.mpr hT
  positivity

/-- A concrete algorithm, with a proved run schedule, primitive execution loss,
switch accounting, and explicit learning rate. No phase regret is assumed. -/
theorem actual_tuned_phase (T : ℕ) (hT : 0 < T) (q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1)
    (hK : (2:ℝ) ≤ Fintype.card I) (l : I → Fin T → ℝ)
    (hl : ∀ i t, 0 ≤ l i t) (hl1 : ∀ i t, l i t ≤ 1) (fallback j : I) :
    let K : ℝ := Fintype.card I
    let b := runCap T K
    let η := rate (Real.log K) (varianceBudget T b K q)
    let A := algorithm T b q η hq hq1
      (rate_pos _ _ (Real.log_pos (by linarith))
        (varianceBudget_pos T b K q hT (by linarith) hq)) (by linarith) l hl hl1
    (∑ h, pathLaw A.kernel T h*taskTotal T b l h fallback)-comparatorTotal T l j/2 ≤
      4*((K*Real.log K)^((1:ℝ)/3)*(T:ℝ)^((2:ℝ)/3)+
        Real.sqrt (K*Real.log K*T/q)+1) := by
  dsimp only
  let K : ℝ := Fintype.card I
  let b := runCap T K
  let V := varianceBudget T b K q
  let η := rate (Real.log K) V
  have hk : 0 < K := by dsimp [K]; linarith
  have hlK : 0 < Real.log K := Real.log_pos (by dsimp [K]; linarith)
  have hv : 0 < V := varianceBudget_pos T b K q hT hk hq
  have heta : 0 < η := rate_pos _ _ hlK hv
  have hb : 0 < b := runCap_pos T K hT
  have hr := expected_task_regret T b hb q η hq hq1 heta hk l hl hl1 fallback j
  change _ ≤ (Real.log K/η+η/2*V+(T:ℝ)/b+1)/2 at hr
  have he := tuned_identity (Real.log K) V hlK hv
  change Real.log K/η+η/2*V=Real.sqrt (2*Real.log K*V) at he
  rw [he] at hr
  let a := K*Real.log K
  have ha : 1 ≤ a := entropy_scale_ge_one K hK
  have hnonneg : 0 ≤ a := by linarith
  have hroot : Real.sqrt (2*Real.log K*V) ≤
      Real.sqrt (2*a*T*(b:ℝ))+Real.sqrt (2*a*T/q) := by
    have hid : 2*Real.log K*V=2*a*T*(b:ℝ)+2*a*T/q := by dsimp [a,V,varianceBudget]; ring
    rw [hid]
    exact sqrt_sum_bound _ _ (by positivity) (by positivity)
  have htune := corrected_phase_bound a q T ha (by omega) hq hq1
  change Real.sqrt (2*a*T*(b:ℝ))+Real.sqrt (2*a*T/q)+(T:ℝ)/b+2 ≤ _ at htune
  have hzero : 0 ≤ Real.sqrt (2*a*T*(b:ℝ))+Real.sqrt (2*a*T/q)+(T:ℝ)/b := by positivity
  change _ ≤ 4*(a^((1:ℝ)/3)*(T:ℝ)^((2:ℝ)/3)+Real.sqrt (a*T/q)+1)
  exact le_trans hr (by nlinarith)

end DRGPR.TunedPhase
#print axioms DRGPR.TunedPhase.entropy_scale_ge_one
#print axioms DRGPR.TunedPhase.rate_pos
#print axioms DRGPR.TunedPhase.tuned_identity
#print axioms DRGPR.TunedPhase.sqrt_sum_bound
#print axioms DRGPR.TunedPhase.runCap_pos
#print axioms DRGPR.TunedPhase.varianceBudget_pos
#print axioms DRGPR.TunedPhase.actual_tuned_phase
