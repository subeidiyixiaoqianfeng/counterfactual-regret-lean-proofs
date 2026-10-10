import NativeNoRegret

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace DRGPR.NativeFamily
open NativeSemantics

/-- Comparator-dependent couplings need not be the same measure. Only the
specified native learner marginal is shared. This matches the paper's Γ_μ. -/
theorem own_coupling_counterfactual
    {X : ℕ → Type*} [∀ t, MeasurableSpace (X t)]
    {Ω : Type*} [MeasurableSpace Ω] {M : Type*} [Nonempty M] {T : ℕ}
    (Γ : M → Measure Ω) [∀ m, IsProbabilityMeasure (Γ m)]
    (I : M → Ω → ℕ → Type*) [∀ m ω r, Fintype (I m ω r)]
    (A : Execution X T) (C : M → Execution X T)
    (E : ∀ m, DependentTransfer.Experiment Ω (I m) (Γ m))
    (B : ModelMain.Budget) (η code : ℝ)
    (W : ∀ m, Witness A (C m) (E m) B)
    (hη : ∀ m, (E m).η = η) (hc : ∀ m, (E m).C = code) :
    A.expectedLoss - sInf (Set.range (fun m => (C m).expectedLoss)) ≤
      B.bound η code := by
  apply DRGPR.infimum_transfer A.expectedLoss (B.bound η code) _
  · exact Set.range_nonempty _
  · intro x hx
    obtain ⟨m, rfl⟩ := hx
    simpa [hη m, hc m] using native_transfer A (C m) (E m) B (W m)

theorem own_coupling_no_regret
    {X : ℕ → Type*} [∀ t, MeasurableSpace (X t)]
    {Ω : Type*} [MeasurableSpace Ω] {M : Type*} [Nonempty M]
    (Γ : ℕ → M → Measure Ω) [∀ n m, IsProbabilityMeasure (Γ n m)]
    (I : ℕ → M → Ω → ℕ → Type*) [∀ n m ω r, Fintype (I n m ω r)]
    (T : ℕ → ℕ) (hT : ∀ n, 0 < T n)
    (A : ∀ n, Execution X (T n)) (C : ∀ n, M → Execution X (T n))
    (E : ∀ n m, DependentTransfer.Experiment Ω (I n m) (Γ n m))
    (B : ℕ → ModelMain.Budget) (η code : ℕ → ℝ)
    (W : ∀ n m, Witness (A n) (C n m) (E n m) (B n))
    (hη : ∀ n m, (E n m).η = η n) (hc : ∀ n m, (E n m).C = code n)
    (hBT : ∀ n, (B n).T = T n)
    (hb : Tendsto (fun n => (B n).bound (η n) (code n)/(B n).T) atTop (𝓝 0)) :
    Tendsto (fun n => max 0
      (((A n).expectedLoss - sInf (Set.range (fun m => (C n m).expectedLoss)))/(T n:ℝ)))
      atTop (𝓝 0) := by
  apply NativeNoRegret.upper_no_regret _ (fun n => (B n).bound (η n) (code n)) _
    (fun n => Nat.cast_pos.mpr (hT n))
  · intro n
    exact own_coupling_counterfactual (Γ n) (I n) (A n) (C n) (E n)
      (B n) (η n) (code n) (W n) (hη n) (hc n)
  · simpa only [hBT] using hb

end DRGPR.NativeFamily
#print axioms DRGPR.NativeFamily.own_coupling_counterfactual
#print axioms DRGPR.NativeFamily.own_coupling_no_regret
