import PrimitiveUniversalPhase

noncomputable section
open scoped BigOperators
namespace DRGPR.PrimitiveTunedPhase
open SupportedInformation TunedPhase PhaseTuning PrimitiveTaskRegret PrimitiveUniversalPhase
variable {I : Type} [Fintype I] [DecidableEq I]

/-- The clipped integer cap cannot make the last-tail ledger larger than
the already budgeted switching scale, up to two primitive rounds. -/
theorem cap_tail_bound (a : ℝ) (n : ℕ) (ha : 1 ≤ a) (hn : 0 < n) :
    let b := cap n (((n:ℝ)/a)^((1:ℝ)/3))
    (b:ℝ) ≤ (n:ℝ)/b+2 := by
  let x := ((n:ℝ)/a)^((1:ℝ)/3)
  let b := cap n x
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
  have ha0 : 0 < a := by linarith
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  obtain ⟨hx,hcube⟩ := root_pos_cube a n ha0 hn0
  change 0 < x at hx
  change a*x^3=(n:ℝ) at hcube
  have hxn := root_le_n a n x ha hnR hx hcube
  obtain ⟨hbx,hbhi⟩ := cap_bounds n x hx hxn
  change x ≤ (b:ℝ) at hbx
  change (b:ℝ) < x+1 at hbhi
  have hbpos : (0:ℝ) < b := hx.trans_le hbx
  have hb1 : (1:ℝ) ≤ b := by exact_mod_cast (show 1 ≤ b from Nat.one_le_iff_ne_zero.mpr (Nat.cast_ne_zero.mp hbpos.ne'))
  have hx2 : x^2 ≤ (n:ℝ) := by
    by_cases h : x ≤ 1
    · have hp := mul_nonneg hx.le (sub_nonneg.mpr h)
      nlinarith
    · have h1 : 1 ≤ x := le_of_not_ge h
      have hp := mul_nonneg (sub_nonneg.mpr ha) (pow_nonneg hx.le 3)
      have hq := mul_nonneg (sq_nonneg x) (sub_nonneg.mpr h1)
      nlinarith
  have hsq : ((b:ℝ)-1)^2 ≤ x^2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
  change (b:ℝ) ≤ (n:ℝ)/b+2
  have hb2 : (b:ℝ)^2 ≤ (n:ℝ)+2*b := by nlinarith
  have hh : ((b:ℝ)-2)*b ≤ n := by nlinarith
  have hd := (le_div_iff₀ hbpos).mpr hh
  linarith

/-- Same numerical phase rate, now for the actual primitive-transcript
algorithm and every fixed Boolean loss table at an arbitrary horizon. -/
theorem tuned_primitive_phase (label : I → ℕ) (n : ℕ) (hn : 0 < n)
    (table : Hist (I → Bool) n) (q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1)
    (hK : (2:ℝ) ≤ Fintype.card I) (f j : I) :
    let K : ℝ := Fintype.card I
    let b := runCap n K
    let η := rate (Real.log K) (varianceBudget n b K q)
    let p := PhaseAlgorithm.uniform (by linarith : (0:ℝ) < Fintype.card I)
    (∑ a, ObliviousFactorization.playerWeight
      (ObliviousInformation.choice (PrimitiveRun.algorithm q η b p f).p q) n table a *
      taskTotal label n table a)-ObliviousMinimax.tableTotal j n table/2 ≤
      4*((K*Real.log K)^((1:ℝ)/3)*(n:ℝ)^((2:ℝ)/3)+Real.sqrt (K*Real.log K*n/q)+1) := by
  dsimp only
  let K : ℝ := Fintype.card I
  let b := runCap n K
  let V := varianceBudget n b K q
  let η := rate (Real.log K) V
  have hk : 0 < K := by dsimp [K]; linarith
  have hlK : 0 < Real.log K := Real.log_pos (by dsimp [K]; linarith)
  have hv : 0 < V := varianceBudget_pos n b K q hn hk hq
  have heta : 0 < η := rate_pos _ _ hlK hv
  have hb : 0 < b := runCap_pos n K hn
  have hr := universal_phase_bound label n b hn hb table q η hq hq1 heta
    (PhaseAlgorithm.uniform hk) (PhaseAlgorithm.uniform_pos hk) f j
  rw [PhaseAlgorithm.uniform_code] at hr
  change _ ≤ (Real.log K/η+η/2*V+(n:ℝ)/b+b+1)/2 at hr
  have he := tuned_identity (Real.log K) V hlK hv
  change Real.log K/η+η/2*V=Real.sqrt (2*Real.log K*V) at he
  rw [he] at hr
  let a := K*Real.log K
  have ha : 1 ≤ a := entropy_scale_ge_one K hK
  have hroot : Real.sqrt (2*Real.log K*V) ≤ Real.sqrt (2*a*n*(b:ℝ))+Real.sqrt (2*a*n/q) := by
    have hid : 2*Real.log K*V=2*a*n*(b:ℝ)+2*a*n/q := by dsimp [a,V,varianceBudget]; ring
    rw [hid]
    exact sqrt_sum_bound _ _ (by positivity) (by positivity)
  have htune := corrected_phase_bound a q n ha (by omega) hq hq1
  change Real.sqrt (2*a*n*(b:ℝ))+Real.sqrt (2*a*n/q)+(n:ℝ)/b+2 ≤ _ at htune
  have htail := cap_tail_bound a n ha hn
  change (b:ℝ) ≤ (n:ℝ)/b+2 at htail
  have hzero : 0 ≤ Real.sqrt (2*a*n*(b:ℝ))+Real.sqrt (2*a*n/q) := by positivity
  change _ ≤ 4*(a^((1:ℝ)/3)*(n:ℝ)^((2:ℝ)/3)+Real.sqrt (a*n/q)+1)
  exact hr.trans (by linarith)

end DRGPR.PrimitiveTunedPhase
#print axioms DRGPR.PrimitiveTunedPhase.cap_tail_bound
#print axioms DRGPR.PrimitiveTunedPhase.tuned_primitive_phase
