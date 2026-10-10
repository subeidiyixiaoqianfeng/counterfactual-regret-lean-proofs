import StateFeedbackStability
import NativeNoRegret

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology
namespace DRGPR.NativeRepairEndpoint
open LocalFeedbackStability FeedbackTrajectory
variable {I : ℕ → Type} [∀ t, Fintype (I t)]

/-- All additional fields are local transition, local influence, or actual
pathwise resource conditions. No accumulated loss or regret bound is a field. -/
structure Side (K L : Dynamics I) (c : (t : ℕ) → I t → ℝ)
    (p : FiniteController.Dist (I 0)) (T : ℕ) (H eps cmin B : ℝ) where
  stability : StateFeedbackStability.Contract K L c T
  activity : (t : ℕ) → I t → ℝ
  resource : (t : ℕ) → I t → ℝ
  influence_le : ∀ t s, stability.influence t s ≤ H
  error_le : ∀ t s, stability.epsilon t s ≤ eps*activity t s
  resource_le : ∀ t s, cmin*activity t s ≤ resource t s
  hard : ∀ s h, 0 < p.val s*weight K 0 T s h → loss resource 0 T s h ≤ B

theorem Side.gap (K L : Dynamics I) (c : (t : ℕ) → I t → ℝ)
    (p : FiniteController.Dist (I 0)) (T : ℕ) (H eps cmin B : ℝ)
    (hH : 0 ≤ H) (he : 0 ≤ eps) (hc : 0 < cmin)
    (D : Side K L c p T H eps cmin B) :
    |expected K c p T-expected L c p T| ≤ H*eps*B/cmin :=
  StateFeedbackStability.adaptive_resource_loss K L c p T D.stability
    D.activity D.resource H eps cmin B hH he hc D.influence_le D.error_le D.resource_le D.hard

/-- The original native kernels need not implement the reference selector.
The reference theorem is invoked, not postulated as a regret assumption. -/
theorem counterfactual
    {Ω : Type*} [MeasurableSpace Ω] {M : Type*} [Nonempty M]
    (Γ : M → Measure Ω) [∀ m, IsProbabilityMeasure (Γ m)]
    (J : M → Ω → ℕ → Type*) [∀ m ω r, Fintype (J m ω r)]
    (KA LA : Dynamics I) (KC LC : M → Dynamics I)
    (c : (t : ℕ) → I t → ℝ) (p : FiniteController.Dist (I 0)) (T : ℕ)
    (H eps cmin BA BC : ℝ) (hH : 0 ≤ H) (he : 0 ≤ eps) (hc : 0 < cmin)
    (DA : Side KA LA c p T H eps cmin BA)
    (DC : ∀ m, Side (KC m) (LC m) c p T H eps cmin BC)
    (E : ∀ m, DependentTransfer.Experiment Ω (J m) (Γ m)) (B : ModelMain.Budget)
    (W : ∀ m, ModelMain.Certificates (E m) B) (η code : ℝ)
    (hη : ∀ m, (E m).η = η) (hcode : ∀ m, (E m).C = code)
    (hA : ∀ m, (∫ ω, (W m).realA ω ∂(Γ m)) = expected LA c p T)
    (hC : ∀ m, (∫ ω, (W m).realM ω ∂(Γ m)) = expected (LC m) c p T) :
    expected KA c p T - sInf (Set.range (fun m => expected (KC m) c p T)) ≤
      B.bound η code + H*eps*(BA+BC)/cmin := by
  apply DRGPR.infimum_transfer
  · exact Set.range_nonempty _
  · rintro _ ⟨m,rfl⟩
    have hm := ModelMain.main_fixed (E m) B (W m)
    rw [hA m,hC m,hη m,hcode m] at hm
    have ha := (abs_le.mp (Side.gap KA LA c p T H eps cmin BA hH he hc DA)).2
    have hd := (abs_le.mp (Side.gap (KC m) (LC m) c p T H eps cmin BC hH he hc (DC m))).1
    have hr : H*eps*(BA+BC)/cmin = H*eps*BA/cmin+H*eps*BC/cmin := by ring
    rw [hr]
    linarith

/-- Rate endpoint for a fixed local influence constant and growing hard
budgets. The pointwise input is supplied by counterfactual above. -/
theorem no_regret (R U BA BC T : ℕ → ℝ) (k : ℝ)
    (hT : ∀ n, 0 < T n)
    (hpoint : ∀ n, R n ≤ U n+k*(BA n+BC n))
    (hu : Tendsto (fun n => U n/T n) atTop (𝓝 0))
    (ha : Tendsto (fun n => BA n/T n) atTop (𝓝 0))
    (hc : Tendsto (fun n => BC n/T n) atTop (𝓝 0)) :
    Tendsto (fun n => max 0 (R n/T n)) atTop (𝓝 0) := by
  apply NativeNoRegret.upper_no_regret R _ T hT hpoint
  have hh := hu.add ((ha.add hc).const_mul k)
  convert hh using 1 <;> try norm_num
  funext n
  ring

end DRGPR.NativeRepairEndpoint
#print axioms DRGPR.NativeRepairEndpoint.Side.gap
#print axioms DRGPR.NativeRepairEndpoint.counterfactual
#print axioms DRGPR.NativeRepairEndpoint.no_regret
