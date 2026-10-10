import FeedbackTrajectory

/-! Composes the new local feedback contract with the existing proved
reference regret theorem. The feedback arrow is counted once, outside the
reference certificate. It must not already be included in that certificate.
Hard comparator admissibility and reference realization remain explicit
model-interface obligations, not consequences of TV stability. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology
namespace DRGPR.FeedbackRepairMain
open LocalFeedbackStability FeedbackTrajectory
variable {I : ℕ → Type} [∀ t, Fintype (I t)]

theorem resource_bound {K L : Dynamics I} {c : (t : ℕ) → I t → ℝ} {T : ℕ}
    (C : Contract K L c T) (activity cost : ℕ → ℝ)
    (H eps cmin B : ℝ) (hH : 0 ≤ H) (heps : 0 ≤ eps) (hcmin : 0 < cmin)
    (hi : ∀ t, C.influence t ≤ H)
    (he : ∀ t, C.epsilon t ≤ eps*activity t)
    (hcost : ∀ t, cmin*activity t ≤ cost t)
    (hbudget : charge cost 0 T ≤ B) :
    C.budget ≤ H*eps*B/cmin := by
  have hlocal : ∀ t, C.influence t*C.epsilon t ≤ (H*eps)*activity t := by
    intro t
    calc
      _ ≤ H*C.epsilon t :=
        mul_le_mul_of_nonneg_right (hi t) (C.epsilon_nonneg t)
      _ ≤ H*(eps*activity t) := mul_le_mul_of_nonneg_left (he t) hH
      _ = _ := by ring
  have hb := charge_mono _ _ hcost 0 T
  rw [charge_const_mul] at hb
  have hcount : charge activity 0 T ≤ B/cmin :=
    (le_div_iff₀ hcmin).mpr (by nlinarith [hb.trans hbudget])
  have hh := charge_mono _ _ hlocal 0 T
  rw [charge_const_mul] at hh
  calc
    C.budget ≤ (H*eps)*charge activity 0 T := hh
    _ ≤ (H*eps)*(B/cmin) := mul_le_mul_of_nonneg_left hcount (mul_nonneg hH heps)
    _ = _ := by ring

/-- Local stability is required for every comparator on its own process.
Only the comparator error bound is uniform. No equality of their generated
libraries or their counterfactual histories is assumed. -/
theorem repaired_counterfactual
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {J : Ω → ℕ → Type*} [∀ ω r, Fintype (J ω r)]
    {M : Type*} [Nonempty M]
    (KA LA : Dynamics I) (KC LC : M → Dynamics I)
    (c : (t : ℕ) → I t → ℝ) (p : FiniteController.Dist (I 0)) (T : ℕ)
    (CA : Contract KA LA c T) (CC : ∀ m, Contract (KC m) (LC m) c T)
    (E : M → DependentTransfer.Experiment Ω J μ) (B : ModelMain.Budget)
    (W : ∀ m, ModelMain.Certificates (E m) B) (η code EC : ℝ)
    (hη : ∀ m, (E m).η = η) (hcode : ∀ m, (E m).C = code)
    (hA : ∀ m, (∫ ω, (W m).realA ω ∂μ) = expected LA c p T)
    (hC : ∀ m, (∫ ω, (W m).realM ω ∂μ) = expected (LC m) c p T)
    (hCC : ∀ m, (CC m).budget ≤ EC) :
    expected KA c p T - sInf (Set.range (fun m => expected (KC m) c p T)) ≤
      B.bound η code + CA.budget + EC := by
  apply DRGPR.infimum_transfer
  · exact Set.range_nonempty _
  · intro x hx
    obtain ⟨m,rfl⟩ := hx
    have hmain := ModelMain.main_fixed (E m) B (W m)
    rw [hA m,hC m,hη m,hcode m] at hmain
    have ha := (abs_le.mp (local_to_actual_loss KA LA c p T CA)).2
    have hc := (abs_le.mp (local_to_actual_loss (KC m) (LC m) c p T (CC m))).1
    linarith [hCC m]

/-- An explicit asymptotic consequence of hard resource scaling. It is not
obtained by assuming that the final regret itself is sublinear. -/
theorem resource_rate (budget horizon : ℕ → ℝ) (H eps cmin : ℝ)
    (hb : Tendsto (fun n => budget n/horizon n) atTop (𝓝 0)) :
    Tendsto (fun n => (H*eps*budget n/cmin)/horizon n) atTop (𝓝 0) := by
  have he : ∀ n, (H*eps*budget n/cmin)/horizon n =
      (H*eps/cmin)*(budget n/horizon n) := by intro n; ring
  simp_rw [he]
  simpa using (tendsto_const_nhds.mul hb :
    Tendsto (fun n => (H*eps/cmin)*(budget n/horizon n)) atTop (𝓝 ((H*eps/cmin)*0)))

theorem repaired_no_regret (regret core ea ec horizon : ℕ → ℝ)
    (hT : ∀ n, 0 < horizon n)
    (hu : ∀ n, regret n ≤ core n+ea n+ec n)
    (hcore : Tendsto (fun n => core n/horizon n) atTop (𝓝 0))
    (ha : Tendsto (fun n => ea n/horizon n) atTop (𝓝 0))
    (hc : Tendsto (fun n => ec n/horizon n) atTop (𝓝 0)) :
    Tendsto (fun n => max 0 (regret n/horizon n)) atTop (𝓝 0) := by
  apply NativeNoRegret.upper_no_regret regret (fun n => core n+ea n+ec n) horizon hT hu
  have hh := (hcore.add ha).add hc
  simpa only [add_div,add_zero] using hh

end DRGPR.FeedbackRepairMain
#print axioms DRGPR.FeedbackRepairMain.resource_bound
#print axioms DRGPR.FeedbackRepairMain.repaired_counterfactual
#print axioms DRGPR.FeedbackRepairMain.resource_rate
#print axioms DRGPR.FeedbackRepairMain.repaired_no_regret
