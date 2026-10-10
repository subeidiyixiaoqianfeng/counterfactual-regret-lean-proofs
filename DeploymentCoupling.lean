import GeneralSelection
import Mathlib.Order.Interval.Finset.Nat

/-!
Original v9, equations cpcertificate and cppersistent.
The probability measure below is a coupling of two complete executions.
The window/first-divergence contract is an explicit premise, not a theorem
that a native agent follows the reference Bandit. No external controller is
introduced. Time is zero-based, so the persistent coefficient is T - t.
-/
noncomputable section
open MeasureTheory Finset
open scoped BigOperators
namespace DRGPR.DeploymentCoupling

variable {Ω : Type*} [MeasurableSpace Ω]
variable {ι : Type*} [Fintype ι]

/-- Integrate a complete-process influence bound, then count how often each
innovation can affect a scored round. All expectations use the same coupling. -/
theorem weighted_coupling (μ : Measure Ω) [IsProbabilityMeasure μ]
    (realLoss refLoss innovation : ι → Ω → ℝ)
    (a : ι → ι → ℝ) (δ ζ C : ι → ℝ)
    (hr : ∀ s, Integrable (realLoss s) μ)
    (hf : ∀ s, Integrable (refLoss s) μ)
    (hi : ∀ t, Integrable (innovation t) μ)
    (ha : ∀ s t, 0 ≤ a s t)
    (hδ : ∀ t, 0 ≤ δ t)
    (hmean : ∀ t, (∫ ω, innovation t ω ∂μ) ≤ δ t)
    (hpath : ∀ s, ∀ᵐ ω ∂μ,
      |realLoss s ω - refLoss s ω| ≤
        (∑ t, a s t * innovation t ω) + ζ s)
    (hcount : ∀ t, (∑ s, a s t) ≤ C t) :
    |(∫ ω, ∑ s, realLoss s ω ∂μ) -
      (∫ ω, ∑ s, refLoss s ω ∂μ)| ≤
      (∑ t, C t * δ t) + ∑ s, ζ s := by
  have hlocal (s : ι) :
      |(∫ ω, realLoss s ω ∂μ) - (∫ ω, refLoss s ω ∂μ)| ≤
        (∑ t, a s t * δ t) + ζ s := by
    have hs : Integrable (fun ω => ∑ t, a s t * innovation t ω) μ :=
      integrable_finset_sum _ (fun t _ => (hi t).const_mul (a s t))
    calc
      _ = |∫ ω, realLoss s ω - refLoss s ω ∂μ| := by
        rw [integral_sub (hr s) (hf s)]
      _ ≤ ∫ ω, |realLoss s ω - refLoss s ω| ∂μ :=
        abs_integral_le_integral_abs
      _ ≤ ∫ ω, (∑ t, a s t * innovation t ω) + ζ s ∂μ :=
        integral_mono_ae ((hr s).sub (hf s)).abs
          (hs.add (integrable_const _)) (hpath s)
      _ = (∑ t, a s t * ∫ ω, innovation t ω ∂μ) + ζ s := by
        rw [integral_add hs (integrable_const _),
          integral_finset_sum _ (fun t _ => (hi t).const_mul (a s t))]
        simp [integral_const_mul]
      _ ≤ _ := add_le_add_right
        (sum_le_sum (fun t _ => mul_le_mul_of_nonneg_left (hmean t) (ha s t))) _
  calc
    _ = |∑ s, ((∫ ω, realLoss s ω ∂μ) - ∫ ω, refLoss s ω ∂μ)| := by
      rw [integral_finset_sum _ (fun s _ => hr s),
        integral_finset_sum _ (fun s _ => hf s), sum_sub_distrib]
    _ ≤ ∑ s, |(∫ ω, realLoss s ω ∂μ) - ∫ ω, refLoss s ω ∂μ| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s, ((∑ t, a s t * δ t) + ζ s) :=
      sum_le_sum (fun s _ => hlocal s)
    _ = (∑ t, (∑ s, a s t) * δ t) + ∑ s, ζ s := by
      rw [sum_add_distrib, sum_comm]
      simp_rw [sum_mul]
    _ ≤ _ := add_le_add_right
      (sum_le_sum (fun t _ => mul_le_mul_of_nonneg_right (hcount t) (hδ t))) _

/-- A finite-memory innovation at time t can affect only L+1 rounds.
Clipping the window at the horizon can only decrease this count. -/
theorem window_count (T L : ℕ) (t : Fin T) :
    (∑ s : Fin T, if t.val ≤ s.val ∧ s.val ≤ t.val + L then (1 : ℝ) else 0)
      ≤ (L + 1 : ℕ) := by
  rw [Fin.sum_univ_eq_sum_range
    (fun s : ℕ => if t.val ≤ s ∧ s ≤ t.val + L then (1 : ℝ) else 0) T]
  have hsub : (range T).filter (fun s => t.val ≤ s ∧ s ≤ t.val + L)
      ⊆ Icc t.val (t.val + L) := by
    intro s hs
    exact mem_Icc.mpr (mem_filter.mp hs).2
  have hc := card_le_card hsub
  have he : ((Icc t.val (t.val + L)).card : ℕ) = L + 1 := by
    rw [Nat.card_Icc]
    omega
  rw [he] at hc
  have hsum :
      (∑ s ∈ range T, if t.val ≤ s ∧ s ≤ t.val + L then (1 : ℝ) else 0) =
      (((range T).filter (fun s => t.val ≤ s ∧ s ≤ t.val + L)).card : ℝ) := by
    rw [← sum_filter]
    simp
  simpa only [hsum] using (Nat.cast_le (α := ℝ)).mpr hc

theorem persistent_count (T : ℕ) (t : Fin T) :
    (∑ s : Fin T, if t.val ≤ s.val then (1 : ℝ) else 0) =
      (T - t.val : ℕ) := by
  rw [Fin.sum_univ_eq_sum_range
    (fun s : ℕ => if t.val ≤ s then (1 : ℝ) else 0) T]
  have he : (range T).filter (fun s => t.val ≤ s) = Ico t.val T := by
    ext s
    simp only [mem_filter, mem_range, mem_Ico]
    omega
  rw [← sum_filter, he]
  simp

theorem finite_influence (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T L : ℕ) (realLoss refLoss innovation : Fin T → Ω → ℝ)
    (δ ζ : Fin T → ℝ)
    (hr : ∀ s, Integrable (realLoss s) μ)
    (hf : ∀ s, Integrable (refLoss s) μ)
    (hi : ∀ t, Integrable (innovation t) μ)
    (hδ : ∀ t, 0 ≤ δ t)
    (hmean : ∀ t, (∫ ω, innovation t ω ∂μ) ≤ δ t)
    (hpath : ∀ s, ∀ᵐ ω ∂μ, |realLoss s ω - refLoss s ω| ≤
      (∑ t, (if t.val ≤ s.val ∧ s.val ≤ t.val + L then (1 : ℝ) else 0) *
        innovation t ω) + ζ s) :
    |(∫ ω, ∑ s, realLoss s ω ∂μ) -
      (∫ ω, ∑ s, refLoss s ω ∂μ)| ≤
      (L + 1 : ℕ) * (∑ t, δ t) + ∑ s, ζ s := by
  simpa only [mul_sum] using
    weighted_coupling μ realLoss refLoss innovation
      (fun s t => if t.val ≤ s.val ∧ s.val ≤ t.val + L then 1 else 0)
      δ ζ (fun _ => (L + 1 : ℕ)) hr hf hi
      (by intros; dsimp; split_ifs <;> norm_num) hδ hmean hpath (window_count T L)

theorem persistent_influence (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : ℕ) (realLoss refLoss innovation : Fin T → Ω → ℝ)
    (δ ζ : Fin T → ℝ)
    (hr : ∀ s, Integrable (realLoss s) μ)
    (hf : ∀ s, Integrable (refLoss s) μ)
    (hi : ∀ t, Integrable (innovation t) μ)
    (hδ : ∀ t, 0 ≤ δ t)
    (hmean : ∀ t, (∫ ω, innovation t ω ∂μ) ≤ δ t)
    (hpath : ∀ s, ∀ᵐ ω ∂μ, |realLoss s ω - refLoss s ω| ≤
      (∑ t, (if t.val ≤ s.val then (1 : ℝ) else 0) * innovation t ω) + ζ s) :
    |(∫ ω, ∑ s, realLoss s ω ∂μ) -
      (∫ ω, ∑ s, refLoss s ω ∂μ)| ≤
      (∑ t, (T - t.val : ℕ) * δ t) + ∑ s, ζ s := by
  exact weighted_coupling μ realLoss refLoss innovation
    (fun s t => if t.val ≤ s.val then 1 else 0)
    δ ζ (fun t => (T - t.val : ℕ)) hr hf hi
    (by intros; dsimp; split_ifs <;> norm_num) hδ hmean hpath
    (fun t => (persistent_count T t).le)

/-- The same complete execution can be measured under its own marginal law or
under a coupling. This is not permission to replace one execution by another. -/
theorem marginal_expectation {X : Type*} [MeasurableSpace X]
    (μ : Measure Ω) (ν : Measure X) (path : Ω → X) (loss : X → ℝ)
    (hp : Measurable path) (hm : μ.map path = ν)
    (hl : Integrable loss ν) :
    (∫ x, loss x ∂ν) = ∫ ω, loss (path ω) ∂μ := by
  subst ν
  exact integral_map hp.aemeasurable hl.aestronglyMeasurable

/-- A first-divergence time beyond the horizon means no scored divergence.
Its indicators are mutually exclusive by construction, not independent. -/
theorem first_event_prefix (T τ : ℕ) (s : Fin T) :
    (∑ t : Fin T, (if t.val ≤ s.val then (1 : ℝ) else 0) *
      (if τ = t.val then (1 : ℝ) else 0)) =
      if τ ≤ s.val then 1 else 0 := by
  by_cases h : τ ≤ s.val
  · let k : Fin T := ⟨τ, lt_of_le_of_lt h s.isLt⟩
    rw [sum_eq_single k]
    · simp [k, h]
    · intro t _ htk
      have ht : τ ≠ t.val := by
        intro he
        apply htk
        apply Fin.ext
        exact he.symm
      simp [ht]
    · simp
  · rw [if_neg h]
    apply sum_eq_zero
    intro t _
    by_cases ht : τ = t.val
    · have hn : ¬ t.val ≤ s.val := by simpa [← ht] using h
      simp [hn]
    · simp [ht]

theorem first_event_integrable (μ : Measure Ω) [IsProbabilityMeasure μ]
    (τ : Ω → ℕ) (hτ : Measurable τ) (t : ℕ) :
    Integrable (fun ω => if τ ω = t then (1 : ℝ) else 0) μ := by
  have hs : MeasurableSet {ω | τ ω = t} := hτ (measurableSet_singleton t)
  apply ((integrable_const (μ := μ) (1 : ℝ)).indicator hs).congr
  apply Filter.Eventually.of_forall
  intro ω
  classical
  by_cases h : τ ω = t <;> simp [h]

omit [MeasurableSpace Ω] in
/-- Before the first divergence only direct scoring error is allowed.
Afterwards unit-bounded losses give a discrepancy at most one. This derives
the pathwise premise of persistent_influence from the original v9 contract. -/
theorem first_divergence_pathwise (T : ℕ) (τ : Ω → ℕ)
    (realLoss refLoss : Fin T → Ω → ℝ) (ζ : Fin T → ℝ)
    (hζ : ∀ s, 0 ≤ ζ s)
    (hbefore : ∀ s ω, s.val < τ ω → |realLoss s ω - refLoss s ω| ≤ ζ s)
    (hunit : ∀ s ω, |realLoss s ω - refLoss s ω| ≤ 1) :
    ∀ s ω, |realLoss s ω - refLoss s ω| ≤
      (∑ t : Fin T, (if t.val ≤ s.val then (1 : ℝ) else 0) *
        (if τ ω = t.val then (1 : ℝ) else 0)) + ζ s := by
  intro s ω
  rw [first_event_prefix]
  by_cases h : τ ω ≤ s.val
  · rw [if_pos h]
    exact le_trans (hunit s ω) (by linarith [hζ s])
  · rw [if_neg h, zero_add]
    exact hbefore s ω (Nat.lt_of_not_ge h)

/-- The original first-divergence certificate, on an arbitrary probability
space with a measurable divergence time and integrable scored executions. -/
theorem first_divergence_certificate (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : ℕ) (τ : Ω → ℕ) (hτ : Measurable τ)
    (realLoss refLoss : Fin T → Ω → ℝ) (δ ζ : Fin T → ℝ)
    (hr : ∀ s, Integrable (realLoss s) μ)
    (hf : ∀ s, Integrable (refLoss s) μ)
    (hδ : ∀ t, 0 ≤ δ t) (hζ : ∀ s, 0 ≤ ζ s)
    (hprob : ∀ t, (∫ ω, if τ ω = t.val then (1 : ℝ) else 0 ∂μ) ≤ δ t)
    (hbefore : ∀ s ω, s.val < τ ω → |realLoss s ω - refLoss s ω| ≤ ζ s)
    (hunit : ∀ s ω, |realLoss s ω - refLoss s ω| ≤ 1) :
    |(∫ ω, ∑ s, realLoss s ω ∂μ) -
      (∫ ω, ∑ s, refLoss s ω ∂μ)| ≤
      (∑ t, (T - t.val : ℕ) * δ t) + ∑ s, ζ s := by
  apply persistent_influence μ T realLoss refLoss
    (fun t ω => if τ ω = t.val then 1 else 0) δ ζ hr hf
    (fun t => first_event_integrable μ τ hτ t.val) hδ hprob
  intro s
  exact Filter.Eventually.of_forall
    (first_divergence_pathwise T τ realLoss refLoss ζ hζ hbefore hunit s)

/-- Unit-bounded per-round discrepancy caps the complete-process gap by T,
independently of how large a separately derived influence certificate is. -/
theorem bounded_loss_cap (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : ℕ) (realLoss refLoss : Fin T → Ω → ℝ)
    (hr : ∀ s, Integrable (realLoss s) μ)
    (hf : ∀ s, Integrable (refLoss s) μ)
    (hunit : ∀ s, ∀ᵐ ω ∂μ, |realLoss s ω - refLoss s ω| ≤ 1) :
    |(∫ ω, ∑ s, realLoss s ω ∂μ) -
      (∫ ω, ∑ s, refLoss s ω ∂μ)| ≤ T := by
  have h := weighted_coupling μ realLoss refLoss (fun _ _ => 0)
    (fun _ _ => 0) (fun _ => 0) (fun _ => 1) (fun _ => 0)
    hr hf (fun _ => integrable_const (0 : ℝ))
    (by intros; exact le_rfl) (by intros; exact le_rfl)
    (by intros; simp)
    (by intro s; simpa using hunit s)
    (by intros; simp)
  simpa using h

theorem first_divergence_capped (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : ℕ) (τ : Ω → ℕ) (hτ : Measurable τ)
    (realLoss refLoss : Fin T → Ω → ℝ) (δ ζ : Fin T → ℝ)
    (hr : ∀ s, Integrable (realLoss s) μ)
    (hf : ∀ s, Integrable (refLoss s) μ)
    (hδ : ∀ t, 0 ≤ δ t) (hζ : ∀ s, 0 ≤ ζ s)
    (hprob : ∀ t, (∫ ω, if τ ω = t.val then (1 : ℝ) else 0 ∂μ) ≤ δ t)
    (hbefore : ∀ s ω, s.val < τ ω → |realLoss s ω - refLoss s ω| ≤ ζ s)
    (hunit : ∀ s ω, |realLoss s ω - refLoss s ω| ≤ 1) :
    |(∫ ω, ∑ s, realLoss s ω ∂μ) -
      (∫ ω, ∑ s, refLoss s ω ∂μ)| ≤
      min (T : ℝ) ((∑ t, (T - t.val : ℕ) * δ t) + ∑ s, ζ s) := by
  exact le_min
    (bounded_loss_cap μ T realLoss refLoss hr hf
      (fun s => Filter.Eventually.of_forall (hunit s)))
    (first_divergence_certificate μ T τ hτ realLoss refLoss δ ζ
      hr hf hδ hζ hprob hbefore hunit)

end DRGPR.DeploymentCoupling
#print axioms DRGPR.DeploymentCoupling.weighted_coupling
#print axioms DRGPR.DeploymentCoupling.window_count
#print axioms DRGPR.DeploymentCoupling.persistent_count
#print axioms DRGPR.DeploymentCoupling.finite_influence
#print axioms DRGPR.DeploymentCoupling.persistent_influence
#print axioms DRGPR.DeploymentCoupling.marginal_expectation
#print axioms DRGPR.DeploymentCoupling.first_event_prefix
#print axioms DRGPR.DeploymentCoupling.first_event_integrable
#print axioms DRGPR.DeploymentCoupling.first_divergence_pathwise
#print axioms DRGPR.DeploymentCoupling.first_divergence_certificate
#print axioms DRGPR.DeploymentCoupling.bounded_loss_cap
#print axioms DRGPR.DeploymentCoupling.first_divergence_capped
