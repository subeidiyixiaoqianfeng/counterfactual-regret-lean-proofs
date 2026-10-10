import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-!
Partial formal companion to "Counterfactual Regret for Reflective Agents".
This file proves named algebraic, analytic, and finite-probability steps.
It does NOT formalize the complete stochastic agent construction, adaptive
transcript KL, or the imported switching-cost lower bound. Hypotheses below
are explicit mathematical inputs, not claims that a deployment satisfies them.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace DRGPR

/-- A finite weighted mean, with no hidden probability assumptions. -/
def mean {ι : Type*} [Fintype ι] (p x : ι → ℝ) : ℝ :=
  ∑ i, p i * x i

theorem mean_sub {ι : Type*} [Fintype ι] (p x y : ι → ℝ) :
    mean p (fun i => x i - y i) = mean p x - mean p y := by
  simp [mean, mul_sub, Finset.sum_sub_distrib]

theorem mean_mono {ι : Type*} [Fintype ι] (p x y : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hxy : ∀ i, x i ≤ y i) :
    mean p x ≤ mean p y := by
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hxy i) (hp i)

theorem mean_const {ι : Type*} [Fintype ι] (p : ι → ℝ)
    (hp : ∑ i, p i = 1) (c : ℝ) :
    mean p (fun _ => c) = c := by
  simp [mean, ← Finset.sum_mul, hp]

/-- Tower rule in a finite model: the joint law is marginal times kernel. -/
theorem finite_tower {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ι → ℝ) (k f : ι → κ → ℝ) :
    (∑ i, p i * ∑ j, k i j * f i j) =
    ∑ i, ∑ j, (p i * k i j) * f i j := by
  simp_rw [Finset.mul_sum, mul_assoc]

/-- The measure-theoretic tower step, using mathlib's proved conditional expectation. -/
theorem integral_tower {Ω : Type*} {m m₀ : MeasurableSpace Ω}
    {μ : @Measure Ω m₀} (hm : m ≤ m₀) [SigmaFinite (μ.trim hm)]
    (f : Ω → ℝ) :
    (∫ x, (μ[f|m]) x ∂μ) = ∫ x, f x ∂μ :=
  integral_condExp hm

/-- Normalized joint probabilities from a marginal and conditional kernel. -/
theorem joint_normalized {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ι → ℝ) (k : ι → κ → ℝ)
    (hp : ∑ i, p i = 1) (hk : ∀ i, ∑ j, k i j = 1) :
    (∑ i, ∑ j, p i * k i j) = 1 := by
  simp_rw [← Finset.mul_sum, hk, mul_one]
  exact hp

/-- The exact cancellation in the accepted-feedback estimator. -/
theorem importance_unbiased (p q z : ℝ) (hp : 0 < p) (hq : 0 < q) :
    p / (p * q) * (q * z) = z := by
  field_simp
  <;> ring

theorem importance_second_cancel (p q d : ℝ) (hp : 0 < p) (hq : 0 < q) :
    p * d ^ 2 / (p ^ 2 * q ^ 2) * q = d ^ 2 / (p * q) := by
  field_simp
  <;> ring

theorem square_bounded (y d : ℝ) (hy : 0 ≤ y) (hyd : y ≤ d) :
    y ^ 2 ≤ d ^ 2 := by
  nlinarith

/-- Conditional second-moment domination, after disintegration on the draw. -/
theorem importance_second_bound (p q d m₂ : ℝ)
    (hp : 0 < p) (hq : 0 < q) (hm : m₂ ≤ q * d ^ 2) :
    p / (p ^ 2 * q ^ 2) * m₂ ≤ d ^ 2 / (p * q) := by
  calc
    p / (p ^ 2 * q ^ 2) * m₂
        ≤ p / (p ^ 2 * q ^ 2) * (q * d ^ 2) :=
      mul_le_mul_of_nonneg_left hm (by positivity)
    _ = d ^ 2 / (p * q) := by field_simp <;> ring

theorem weighted_second_cancel {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (d : ℝ) (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i) :
    (∑ i, p i * (d ^ 2 / (p i * q i))) = d ^ 2 * ∑ i, 1 / q i := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  field_simp [(hp i).ne', (hq i).ne']
  <;> ring

theorem capped_square (d b : ℝ) (hd : 0 ≤ d) (hdb : d ≤ b) :
    d ^ 2 ≤ b * d := by
  nlinarith

theorem accumulated_variance {ι : Type*} [Fintype ι]
    (d k : ι → ℝ) (b V : ℝ)
    (hd : ∀ i, 0 ≤ d i) (hdb : ∀ i, d i ≤ b)
    (hk : ∀ i, 0 ≤ k i) (hb : 0 ≤ b)
    (hV : ∑ i, d i * k i ≤ V) :
    (∑ i, (d i) ^ 2 * k i) ≤ b * V := by
  calc
    (∑ i, (d i) ^ 2 * k i) ≤ ∑ i, (b * d i) * k i := by
      exact Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_right (capped_square (d i) b (hd i) (hdb i)) (hk i)
    _ = b * ∑ i, d i * k i := by simp [Finset.mul_sum, mul_assoc]
    _ ≤ b * V := mul_le_mul_of_nonneg_left hV hb

/-- Global exponential upper bound; no restriction x ≤ 1 is imposed. -/
theorem exp_neg_quadratic (x : ℝ) (hx : 0 ≤ x) :
    Real.exp (-x) ≤ 1 - x + x ^ 2 / 2 := by
  let g : ℝ → ℝ := fun y => y - 1 + Real.exp (-y)
  have dg (y : ℝ) : HasDerivAt g (1 - Real.exp (-y)) y := by
    convert ((hasDerivAt_id y).sub_const 1).add (((hasDerivAt_id y).neg).exp) using 1 <;>
      simp [g] <;> ring
  have mg : MonotoneOn g (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact (continuous_iff_continuousAt.mpr (fun y => (dg y).continuousAt)).continuousOn
    · exact fun y _ => (dg y).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [(dg y).deriv]
      have hy0 : 0 ≤ y := Set.mem_Ici.mp (interior_subset hy)
      have he : Real.exp (-y) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      linarith
  have hg (y : ℝ) (hy : 0 ≤ y) : 0 ≤ g y := by
    have h := mg (by simp) hy hy
    simpa [g] using h
  let f : ℝ → ℝ := fun y => 1 - y + y ^ 2 / 2 - Real.exp (-y)
  have df (y : ℝ) : HasDerivAt f (g y) y := by
    convert (((hasDerivAt_const y (1 : ℝ)).sub (hasDerivAt_id y)).add
      (((hasDerivAt_id y).mul (hasDerivAt_id y)).div_const 2)).sub
      (((hasDerivAt_id y).neg).exp) using 1 <;> simp [f, g, pow_two] <;> ring
  have mf : MonotoneOn f (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact (continuous_iff_continuousAt.mpr (fun y => (df y).continuousAt)).continuousOn
    · exact fun y _ => (df y).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [(df y).deriv]
      exact hg y (Set.mem_Ici.mp (interior_subset hy))
  have h := mf (by simp) hx hx
  have : 0 ≤ f x := by simpa [f] using h
  dsimp [f] at this
  linarith

theorem log_upper (y : ℝ) (hy : 0 < y) : Real.log y ≤ y - 1 :=
  Real.log_le_sub_one_of_pos hy

/-- One-step log-normalizer inequality used in the potential proof. -/
theorem log_normalizer {ι : Type*} [Fintype ι]
    (p z : ι → ℝ) (η : ℝ) (hη : 0 < η)
    (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1)
    (hz : ∀ i, 0 ≤ z i) :
    Real.log (∑ i, p i * Real.exp (-η * z i))
      ≤ -η * mean p z + η ^ 2 / 2 * mean p (fun i => (z i) ^ 2) := by
  classical
  have hex : ∃ i, 0 < p i := by
    by_contra hn
    have hzero : ∀ i, p i = 0 := by
      intro i
      have : ¬ 0 < p i := fun h => hn ⟨i, h⟩
      exact le_antisymm (le_of_not_gt this) (hp i)
    simp [hzero] at hpsum
  obtain ⟨j, hj⟩ := hex
  have hpos : 0 < ∑ i, p i * Real.exp (-η * z i) :=
    Finset.sum_pos' (fun i _ => mul_nonneg (hp i) (Real.exp_pos _).le)
      ⟨j, Finset.mem_univ j, mul_pos hj (Real.exp_pos _)⟩
  have hb : (∑ i, p i * Real.exp (-η * z i)) ≤
      ∑ i, p i * (1 - η * z i + (η * z i) ^ 2 / 2) := by
    apply Finset.sum_le_sum
    intro i _
    apply mul_le_mul_of_nonneg_left _ (hp i)
    simpa [neg_mul] using exp_neg_quadratic (η * z i) (mul_nonneg hη.le (hz i))
  have heq : (∑ i, p i * (1 - η * z i + (η * z i) ^ 2 / 2)) =
      1 - η * mean p z + η ^ 2 / 2 * mean p (fun i => (z i) ^ 2) := by
    calc
      (∑ i, p i * (1 - η * z i + (η * z i) ^ 2 / 2)) =
          ∑ i, (p i - η * (p i * z i) + η ^ 2 / 2 * (p i * (z i)^2)) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = 1 - η * mean p z + η ^ 2 / 2 * mean p (fun i => (z i)^2) := by
        simp [mean, Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.mul_sum, hpsum]
  have hl := log_upper (∑ i, p i * Real.exp (-η * z i)) hpos
  rw [heq] at hb
  linarith

/-- Algebraic final step of the deterministic path-potential proof. -/
theorem potential_rearrange (η logW logQ learner comparator second : ℝ)
    (hη : 0 < η)
    (hl : logQ - η * comparator ≤ logW)
    (hu : logW ≤ -η * learner + η ^ 2 / 2 * second) :
    learner - comparator ≤ -logQ / η + η / 2 * second := by
  have he : η * (-logQ / η) = -logQ := by field_simp <;> ring
  have hm : η * (learner - comparator) ≤ η * (-logQ / η + η / 2 * second) := by
    nlinarith
  exact (mul_le_mul_left hη).mp hm

/-- A stochastic transition preserves total unnormalized expert mass. -/
theorem transition_mass {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a : ι → ℝ) (P : ι → κ → ℝ)
    (hP : ∀ i, ∑ j, P i j = 1) :
    (∑ j, ∑ i, a i * P i j) = ∑ i, a i := by
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, hP, mul_one]

/-- Sharing gives every newly eligible identity positive mass. -/
theorem newborn_positive (α ν old : ℝ) (hα : 0 < α) (hν : 0 < ν)
    (hnew : old = 0) :
    0 < (1 - α) * old + α * ν := by
  rw [hnew]
  nlinarith

/-- The eight directed endpoint differences cancel, without probabilistic assumptions. -/
theorem telescope_eight (a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ : ℝ) :
    a₀ - a₈ =
      (a₀-a₁) + (a₁-a₂) + (a₂-a₃) + (a₃-a₄) +
      (a₄-a₅) + (a₅-a₆) + (a₆-a₇) + (a₇-a₈) := by ring

theorem transfer_eight (a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ : ℝ)
    (e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ : ℝ)
    (h₁ : a₀-a₁ ≤ e₁) (h₂ : a₁-a₂ ≤ e₂) (h₃ : a₂-a₃ ≤ e₃)
    (h₄ : a₃-a₄ ≤ e₄) (h₅ : a₄-a₅ ≤ e₅) (h₆ : a₅-a₆ ≤ e₆)
    (h₇ : a₆-a₇ ≤ e₇) (h₈ : a₇-a₈ ≤ e₈) :
    a₀-a₈ ≤ e₁+e₂+e₃+e₄+e₅+e₆+e₇+e₈ := by linarith

/-- Taking the infimum outside expectation needs no attained optimum. -/
theorem infimum_transfer (learner U : ℝ) (values : Set ℝ)
    (hne : values.Nonempty) (h : ∀ c ∈ values, learner - c ≤ U) :
    learner - sInf values ≤ U := by
  have hb : learner - U ≤ sInf values := le_csInf hne (by
    intro c hc
    linarith [h c hc])
  linarith

theorem main_endpoint_bound (realA refA zA zV zAligned zClean refPath refM realM : ℝ)
    (F P D_A D_C G E_nf E_cpA E_cpC C η b V H S : ℝ)
    (h₁ : realA - refA ≤ E_cpA)
    (h₂ : refA - zA ≤ F + P + D_A)
    (h₃ : zA - zV ≤ C / η + η * b * V / 2)
    (h₄ : zV - zAligned ≤ G)
    (h₅ : zAligned - zClean ≤ b * S)
    (h₆ : zClean - refPath ≤ H * (S + 1) + D_C)
    (h₇ : refPath - refM ≤ E_nf)
    (h₈ : refM - realM ≤ E_cpC) :
    realA - realM ≤
      (F + G + D_A + D_C + E_nf + (E_cpA + E_cpC)) +
      C / η + η * b * V / 2 + P + b * S + H * (S + 1) := by
  linarith

theorem budget_gap_nonnegative (hard meanOpt : ℝ) (h : meanOpt ≤ hard) :
    0 ≤ hard - meanOpt := sub_nonneg.mpr h

theorem budget_change_identity (learner hard meanOpt : ℝ) :
    learner - meanOpt = (learner - hard) + (hard - meanOpt) := by ring

theorem not_separate_infima_example :
    min ((0 : ℝ) + 1) (1 + 0) > min (0 : ℝ) 1 + min (1 : ℝ) 0 := by norm_num

/-- Finite conditional-hazard induction; independence is not assumed. -/
theorem failure_geometric (p : ℕ → ℝ) (lam : ℝ) (hlam : lam ≤ 1)
    (h₀ : p 0 ≤ 1) (hstep : ∀ k, p (k+1) ≤ (1-lam) * p k) :
    ∀ k, p k ≤ (1-lam)^k := by
  intro k
  induction k with
  | zero => simpa using h₀
  | succ k ih =>
    calc
      p (k+1) ≤ (1-lam) * p k := hstep k
      _ ≤ (1-lam) * (1-lam)^k := mul_le_mul_of_nonneg_left ih (by linarith)
      _ = (1-lam)^(k+1) := by rw [pow_succ]; ring

theorem coverage_sum {ι : Type*} [Fintype ι]
    (g t : ι → ℝ) (a f T : ℝ)
    (hg : ∀ i, g i ≤ a + t i * f) (ht : ∑ i, t i = T) :
    (∑ i, g i) ≤ Fintype.card ι * a + T * f := by
  calc
    (∑ i, g i) ≤ ∑ i, (a + t i * f) := Finset.sum_le_sum fun i _ => hg i
    _ = Fintype.card ι * a + T * f := by
      simp [Finset.sum_add_distrib, ← Finset.sum_mul, ht]

/-- Summed contraction recurrence, without invoking a geometric-series formula. -/
theorem contraction_sum (β E initial final errors : ℝ)
    (hβ : β < 1) (hi : initial = 0) (hf : 0 ≤ final)
    (hrec : E - initial + final ≤ β * E + errors) :
    E ≤ errors / (1 - β) := by
  apply (le_div_iff₀ (by linarith : 0 < 1 - β)).2
  rw [hi] at hrec
  nlinarith

theorem finite_influence_sum {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a : ι → κ → ℝ) (δ : ι → ℝ) (L : ℝ)
    (h : ∀ i, ∑ j, a i j ≤ L * δ i) :
    (∑ j, ∑ i, a i j) ≤ L * ∑ i, δ i := by
  rw [Finset.sum_comm, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => h i

/-- Diagonal terms alone pay inverse erasure probability. -/
theorem erasure_second_moment_algebra (q sumSquares crossTerms : ℝ) :
    sumSquares / q + crossTerms =
      (sumSquares + crossTerms) + (1/q - 1) * sumSquares := by ring

theorem granular_second_bound (q n L squares : ℝ)
    (hq : 0 < q) (hq1 : q ≤ 1) (hn : 0 ≤ n)
    (hL : L ^ 2 ≤ n ^ 2) (hs : squares ≤ n) :
    L ^ 2 + (1/q - 1) * squares ≤ n ^ 2 + n/q := by
  have hcoef : 0 ≤ 1/q - 1 := by
    have : (1 : ℝ) ≤ 1/q := (le_div_iff₀ hq).2 (by simpa using hq1)
    linarith
  have hm := mul_le_mul_of_nonneg_left hs hcoef
  have he : (1/q - 1) * n = n/q - n := by ring
  linarith

theorem max_le_sum_le_twice_max (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    max x y ≤ x+y ∧ x+y ≤ 2 * max x y := by
  constructor
  · exact max_le (by linarith) (by linarith)
  · have := le_max_left x y
    have := le_max_right x y
    linarith

theorem same_class_lower_bounds (r a b : ℝ) (ha : a ≤ r) (hb : b ≤ r) :
    max a b ≤ r := max_le ha hb

theorem lower_bound_subtract_boundary (r a b c : ℝ)
    (ha : a-c ≤ r) (hb : b-c ≤ r) :
    max a b - c ≤ r := by
  have := max_le (by linarith : a ≤ r+c) (by linarith : b ≤ r+c)
  linarith

theorem saturation_identity (T x y : ℝ) :
    max (min T x) (min T y) = min T (max x y) := by
  rcases le_total x y with h | h
  · rw [max_eq_right h, max_eq_right (min_le_min_left T h)]
  · rw [max_eq_left h, max_eq_left (min_le_min_left T h)]

/-- The last counting step of the information lower bound. -/
theorem information_regret_from_count (n count ε : ℝ)
    (hε : 0 ≤ ε) (hc : count ≤ 3*n/4) :
    ε*n/4 ≤ ε*(n-count) := by
  nlinarith

theorem mean_hard_separation_value (T : ℝ) :
    T - (T+1)/2 = (T-1)/2 := by ring

def bitLoss (b : Bool) : ℝ := if b then 1 else 0

/-- The minimum of two independent Bernoulli(1/2) estimates has mean 1/4. -/
theorem hindsight_minimum_bias :
    (∑ a : Bool, ∑ b : Bool, (1/4 : ℝ) * min (bitLoss a) (bitLoss b)) = 1/4 := by
  norm_num [bitLoss, Fintype.sum_bool]

/-- Stop after a first loss of one, otherwise take one additional sample. -/
theorem stopping_bias_value :
    (∑ a : Bool, ∑ b : Bool,
      (1/4 : ℝ) * (if a then 1 else (bitLoss a + bitLoss b)/2)) = 5/8 := by
  norm_num [bitLoss, Fintype.sum_bool]

/-- Analytic scalar inequality used in the Bernoulli-KL bound. -/
theorem bernoulli_kl_scalar_bound (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1/4) :
    -(1/2 : ℝ) * Real.log (1 - 4*ε^2) ≤ 4*ε^2 := by
  have hx0 : 0 ≤ 4*ε^2 := by positivity
  have hx1 : 4*ε^2 ≤ (1/4 : ℝ) := by nlinarith
  have hd : 0 < 1 - 4*ε^2 := by linarith
  have hl := Real.one_sub_inv_le_log_of_pos hd
  have hi : (1 : ℝ)/(1 - 4*ε^2) ≤ 1 + 2*(4*ε^2) := by
    apply (div_le_iff₀ hd).2
    nlinarith [mul_nonneg hx0 (by linarith : 0 ≤ 1 - 2*(4*ε^2))]
  simp only [one_div] at hi
  linarith

end DRGPR

#print axioms DRGPR.mean_sub
#print axioms DRGPR.mean_mono
#print axioms DRGPR.mean_const
#print axioms DRGPR.finite_tower
#print axioms DRGPR.integral_tower
#print axioms DRGPR.joint_normalized
#print axioms DRGPR.importance_unbiased
#print axioms DRGPR.importance_second_cancel
#print axioms DRGPR.square_bounded
#print axioms DRGPR.importance_second_bound
#print axioms DRGPR.weighted_second_cancel
#print axioms DRGPR.capped_square
#print axioms DRGPR.accumulated_variance
#print axioms DRGPR.exp_neg_quadratic
#print axioms DRGPR.log_upper
#print axioms DRGPR.log_normalizer
#print axioms DRGPR.potential_rearrange
#print axioms DRGPR.transition_mass
#print axioms DRGPR.newborn_positive
#print axioms DRGPR.telescope_eight
#print axioms DRGPR.transfer_eight
#print axioms DRGPR.infimum_transfer
#print axioms DRGPR.main_endpoint_bound
#print axioms DRGPR.budget_gap_nonnegative
#print axioms DRGPR.budget_change_identity
#print axioms DRGPR.not_separate_infima_example
#print axioms DRGPR.failure_geometric
#print axioms DRGPR.coverage_sum
#print axioms DRGPR.contraction_sum
#print axioms DRGPR.finite_influence_sum
#print axioms DRGPR.erasure_second_moment_algebra
#print axioms DRGPR.granular_second_bound
#print axioms DRGPR.max_le_sum_le_twice_max
#print axioms DRGPR.same_class_lower_bounds
#print axioms DRGPR.lower_bound_subtract_boundary
#print axioms DRGPR.saturation_identity
#print axioms DRGPR.information_regret_from_count
#print axioms DRGPR.mean_hard_separation_value
#print axioms DRGPR.hindsight_minimum_bias
#print axioms DRGPR.stopping_bias_value
#print axioms DRGPR.bernoulli_kl_scalar_bound
