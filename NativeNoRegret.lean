import NativeSemantics
import Mathlib.Topology.Order.Basic

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace DRGPR.NativeNoRegret
open NativeSemantics

theorem normalized_budget (B : ModelMain.Budget) (η C : ℝ) :
    B.bound η C / B.T =
      B.delta / B.T + (C/η + η*B.b*B.V/2)/B.T +
      B.prefix/B.T + ((B.b:ℝ)*B.S)/B.T +
      ((B.H:ℝ)*(B.S+1))/B.T := by
  unfold ModelMain.Budget.bound
  ring

/-- Each term names a different contribution already in the main budget.
No additional positive-part penalty is added to the regret definition. -/
theorem budget_tends_zero (B : ℕ → ModelMain.Budget) (η C : ℕ → ℝ)
    (hd : Tendsto (fun n => (B n).delta / (B n).T) atTop (𝓝 0))
    (hs : Tendsto (fun n => (C n/η n + η n*(B n).b*(B n).V/2)/(B n).T)
      atTop (𝓝 0))
    (hp : Tendsto (fun n => (B n).prefix/(B n).T) atTop (𝓝 0))
    (ha : Tendsto (fun n => (((B n).b:ℝ)*(B n).S)/(B n).T) atTop (𝓝 0))
    (hr : Tendsto (fun n => (((B n).H:ℝ)*((B n).S+1))/(B n).T) atTop (𝓝 0)) :
    Tendsto (fun n => (B n).bound (η n) (C n)/(B n).T) atTop (𝓝 0) := by
  simp_rw [normalized_budget]
  simpa using (((hd.add hs).add hp).add ha).add hr

theorem upper_no_regret (regret bound horizon : ℕ → ℝ)
    (hT : ∀ n, 0 < horizon n) (hu : ∀ n, regret n ≤ bound n)
    (hb : Tendsto (fun n => bound n/horizon n) atTop (𝓝 0)) :
    Tendsto (fun n => max 0 (regret n/horizon n)) atTop (𝓝 0) := by
  have hh := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0)).max hb
  simp only [max_self] at hh
  apply squeeze_zero (fun _ => le_max_left _ _) _ hh
  intro n
  exact max_le_max_left 0 (div_le_div_of_nonneg_right (hu n) (hT n).le)

/-- Causal executions, their own-history comparator optimum, the proved
reference selection theorem and normalized budgets compose here.
This is a conditional theorem, not automatic stability of an arbitrary LLM. -/
theorem native_no_regret
    {X : ℕ → Type*} [∀ t, MeasurableSpace (X t)]
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {M : Type*} [Nonempty M]
    (I : ℕ → Ω → ℕ → Type*) [∀ n ω r, Fintype (I n ω r)]
    (T : ℕ → ℕ) (hT : ∀ n, 0 < T n)
    (A : ∀ n, Execution X (T n)) (C : ∀ n, M → Execution X (T n))
    (E : ∀ n, M → DependentTransfer.Experiment Ω (I n) μ)
    (B : ℕ → ModelMain.Budget) (η code : ℕ → ℝ)
    (W : ∀ n m, Witness (A n) (C n m) (E n m) (B n))
    (hη : ∀ n m, (E n m).η = η n) (hc : ∀ n m, (E n m).C = code n)
    (hBT : ∀ n, (B n).T = T n)
    (hb : Tendsto (fun n => (B n).bound (η n) (code n)/(B n).T) atTop (𝓝 0)) :
    Tendsto (fun n => max 0
      (((A n).expectedLoss - sInf (Set.range (fun m => (C n m).expectedLoss)))/(T n:ℝ)))
      atTop (𝓝 0) := by
  apply upper_no_regret _ (fun n => (B n).bound (η n) (code n)) _
    (fun n => Nat.cast_pos.mpr (hT n))
  · intro n
    exact native_counterfactual (A n) (C n) (E n) (B n) (η n) (code n)
      (W n) (hη n) (hc n)
  · simpa only [hBT] using hb

end DRGPR.NativeNoRegret
#print axioms DRGPR.NativeNoRegret.normalized_budget
#print axioms DRGPR.NativeNoRegret.budget_tends_zero
#print axioms DRGPR.NativeNoRegret.upper_no_regret
#print axioms DRGPR.NativeNoRegret.native_no_regret
