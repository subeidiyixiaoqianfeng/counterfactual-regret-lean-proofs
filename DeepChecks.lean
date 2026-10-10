import DRGPR

/-! Counterexamples certify failures of tempting implication steps.
They do not refute the main theorem under all its stated assumptions. -/
noncomputable section
open scoped BigOperators
namespace DRGPR.DeepChecks

def shareStep (α p : ℝ) : ℝ := (1-α)*p + α/2

def shareIter (α p : ℝ) : ℕ → ℝ
  | 0 => p
  | n+1 => shareStep α (shareIter α p n)

theorem share_difference (α p q : ℝ) (n : ℕ) :
    shareIter α p n - shareIter α q n = (1-α)^n * (p-q) := by
  induction n with
  | zero => simp [shareIter]
  | succ n ih =>
    simp only [shareIter, shareStep, pow_succ]
    calc
      (1-α)*shareIter α p n + α/2 - ((1-α)*shareIter α q n + α/2)
        = (1-α)*(shareIter α p n - shareIter α q n) := by ring
      _ = (1-α)*((1-α)^n*(p-q)) := by rw [ih]
      _ = _ := by ring

theorem no_finite_forgetting (α p q : ℝ) (hα : α < 1) (hpq : p ≠ q) (n : ℕ) :
    shareIter α p n ≠ shareIter α q n := by
  apply sub_ne_zero.mp
  rw [share_difference]
  exact mul_ne_zero (pow_pos (sub_pos.mpr hα) n).ne' (sub_ne_zero.mpr hpq)

theorem bernoulli_lower (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (n : ℕ) :
    1 - (n : ℝ)*α ≤ (1-α)^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := mul_le_mul_of_nonneg_left ih (sub_nonneg.mpr hα1)
    have hcross : 0 ≤ (n : ℝ)*α^2 := mul_nonneg (Nat.cast_nonneg n) (sq_nonneg α)
    rw [pow_succ]
    push_cast
    nlinarith

theorem sensitivity_sum (α : ℝ) (n : ℕ) :
    α * (∑ k ∈ Finset.range n, (1-α)^k) = 1-(1-α)^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih, pow_succ]
    ring

theorem slow_memory (T k : ℕ) (hT : 0 < T) (hk : 2*k ≤ T) :
    (1/2 : ℝ) ≤ (1 - 1/(T : ℝ))^k := by
  have hTr : (0 : ℝ) < T := Nat.cast_pos.mpr hT
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hα1 : (1 : ℝ)/T ≤ 1 := (div_le_one hTr).2 hT1
  have hb := bernoulli_lower (1/(T : ℝ)) (by positivity) hα1 k
  have hkr : 2*(k : ℝ) ≤ T := by exact_mod_cast hk
  have hkdiv : (k : ℝ)/T ≤ 1/2 := (div_le_iff₀ hTr).2 (by linarith)
  simp only [mul_one_div] at hb
  linarith

def coinMean (f : Bool → ℝ) : ℝ := (∑ b : Bool, (1/2 : ℝ)*f b)
def clockRounds (fast : Bool) : ℕ := if fast then 2 else 1

theorem common_clock_reveals_draw :
    coinMean (fun b => if b = true ∧ clockRounds b = 2 then 1 else 0) /
      coinMean (fun b => if clockRounds b = 2 then 1 else 0) = 1 := by
  norm_num [coinMean, clockRounds, Fintype.sum_bool]

theorem common_clock_breaks_draw_law :
    coinMean (fun b => if b = true ∧ clockRounds b = 2 then 1 else 0) /
      coinMean (fun b => if clockRounds b = 2 then 1 else 0) ≠ (1/2 : ℝ) := by
  rw [common_clock_reveals_draw]
  norm_num

def twoEstimate (draw coord : Bool) : ℝ := if draw = coord then 2 else 0

theorem fixed_coordinate_unbiased (i : Bool) :
    coinMean (fun draw => twoEstimate draw i) = 1 := by
  cases i <;> norm_num [coinMean, twoEstimate, Fintype.sum_bool]

theorem current_draw_comparator_bias :
    coinMean (fun draw => twoEstimate draw draw) = 2 ∧
      coinMean (fun _ => (1 : ℝ)) = 1 := by
  norm_num [coinMean, twoEstimate, Fintype.sum_bool]

theorem observation_support_not_ignorability :
    coinMean (fun b => if b then 1 else 0) = 1/2 ∧
      coinMean (fun b => (if b then (1 : ℝ) else 0) / (1/2)) = 1 := by
  norm_num [coinMean, Fintype.sum_bool]

theorem target_coverage_obstruction (K n : ℕ) (hK : 0 < K) (hn : 2*n ≤ K) :
    (1/2 : ℝ) ≤ (1 - 1/(K : ℝ))^n := slow_memory K n hK hn

theorem mapped_switch_not_larger {I J : Type*} [DecidableEq I] [DecidableEq J]
    (f : I → J) (x y : I) :
    (if f x ≠ f y then (1 : ℝ) else 0) ≤ (if x ≠ y then (1 : ℝ) else 0) := by
  by_cases h : x = y
  · subst y
    simp
  · split_ifs <;> norm_num

theorem disjoint_support_tv {I : Type*} [Fintype I] (p q : I → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hp1 : ∑ i, p i = 1) (hq1 : ∑ i, q i = 1)
    (disjoint : ∀ i, p i = 0 ∨ q i = 0) :
    (1/2 : ℝ) * (∑ i, |p i - q i|) = 1 := by
  have heq (i : I) : |p i - q i| = p i + q i := by
    rcases disjoint i with h | h
    · simp [h, abs_of_nonneg (hq i)]
    · simp [h, abs_of_nonneg (hp i)]
  simp_rw [heq]
  rw [Finset.sum_add_distrib, hp1, hq1]
  norm_num

theorem disjoint_output_blocks_strict_contraction {I : Type*} [Fintype I]
    (p q : I → ℝ) (β : ℝ) (hβ : β < 1)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hp1 : ∑ i, p i = 1) (hq1 : ∑ i, q i = 1)
    (disjoint : ∀ i, p i = 0 ∨ q i = 0)
    (claimed_contraction : (1/2 : ℝ) * (∑ i, |p i - q i|) ≤ β) : False := by
  rw [disjoint_support_tv p q hp hq hp1 hq1 disjoint] at claimed_contraction
  linarith

end DRGPR.DeepChecks

#print axioms DRGPR.DeepChecks.share_difference
#print axioms DRGPR.DeepChecks.no_finite_forgetting
#print axioms DRGPR.DeepChecks.bernoulli_lower
#print axioms DRGPR.DeepChecks.sensitivity_sum
#print axioms DRGPR.DeepChecks.slow_memory
#print axioms DRGPR.DeepChecks.common_clock_reveals_draw
#print axioms DRGPR.DeepChecks.common_clock_breaks_draw_law
#print axioms DRGPR.DeepChecks.fixed_coordinate_unbiased
#print axioms DRGPR.DeepChecks.current_draw_comparator_bias
#print axioms DRGPR.DeepChecks.observation_support_not_ignorability
#print axioms DRGPR.DeepChecks.target_coverage_obstruction
#print axioms DRGPR.DeepChecks.mapped_switch_not_larger
#print axioms DRGPR.DeepChecks.disjoint_support_tv
#print axioms DRGPR.DeepChecks.disjoint_output_blocks_strict_contraction
