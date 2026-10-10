import LocalGenerationCertificate

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology
namespace DRGPR.LocalNativeFamily
open LocalGenerationCertificate LocalFeedbackStability FeedbackTrajectory

variable {I : Type} [Fintype I] {X : ℕ → Type} [∀ t, Fintype (X t)]
  {Ω : Type*} [MeasurableSpace Ω] {M : Type*} [Nonempty M]
  {D : Type} [Fintype D]
  (Γ : M → Measure Ω) [∀ m, IsProbabilityMeasure (Γ m)]
  (J : M → Ω → ℕ → Type*) [∀ m ω r, Fintype (J m ω r)]

/-- An instance carries local generative and deployment witnesses. It does not
carry a bound on the desired regret, generation gap, or deployment gap. -/
structure Instance where
  KA : Dynamics X
  LA : Dynamics X
  KC : M → Dynamics X
  LC : M → Dynamics X
  score : (t : ℕ) → X t → ℝ
  initial : FiniteController.Dist (X 0)
  horizon : ℕ
  horizon_pos : 0 < horizon
  influence : ℝ
  error : ℝ
  mincost : ℝ
  learnerCost : ℝ
  comparatorCost : ℝ
  influence_nonneg : 0 ≤ influence
  error_nonneg : 0 ≤ error
  mincost_pos : 0 < mincost
  learnerLocal : NativeRepairEndpoint.Side KA LA score initial horizon
    influence error mincost learnerCost
  comparatorLocal : ∀ m, NativeRepairEndpoint.Side (KC m) (LC m) score initial horizon
    influence error mincost comparatorCost
  experiment : ∀ m, DependentTransfer.Experiment Ω (J m) (Γ m)
  budget : ModelMain.Budget
  horizon_eq : budget.T = horizon
  remainder : ∀ m, Remainder (experiment m) budget
  episodes : M → D → Episode I
  endpoint : ∀ m, (experiment m).availableTotal-
    (∫ ω, (remainder m).aligned ω ∂(Γ m)) = ∑ d, (episodes m d).gap
  delay : ℝ
  delta : ℝ
  failure : ℝ
  delta_nonneg : 0 ≤ delta
  failure_nonneg : 0 ≤ failure
  delay_le : ∀ m, (∑ d, ((episodes m d).delay:ℝ)) ≤ delay
  tasks_le : ∀ m, (∑ d, ((episodes m d).tasks:ℝ)) ≤ (horizon:ℝ)
  quality_le : ∀ m d, (episodes m d).delta ≤ delta
  miss_le : ∀ m d, (1-(episodes m d).rho)^(episodes m d).attempts ≤ failure
  generation_budget : budget.G = delay+(horizon:ℝ)*(delta+failure)
  zeroA : budget.E_cpA = 0
  zeroC : budget.E_cpC = 0
  rate : ℝ
  code : ℝ
  rate_eq : ∀ m, (experiment m).η = rate
  code_eq : ∀ m, (experiment m).C = code
  learner_endpoint : ∀ m, (∫ ω, (remainder m).refA ω ∂(Γ m)) =
    expected LA score initial horizon
  comparator_endpoint : ∀ m, (∫ ω, (remainder m).refM ω ∂(Γ m)) =
    expected (LC m) score initial horizon

variable {Γ J}

def Instance.regret (A : Instance (I:=I) (X:=X) (D:=D) Γ J) : ℝ :=
  expected A.KA A.score A.initial A.horizon-
    sInf (Set.range (fun m => expected (A.KC m) A.score A.initial A.horizon))

def Instance.rest (A : Instance (I:=I) (X:=X) (D:=D) Γ J) : ℝ :=
  A.budget.bound A.rate A.code-A.budget.G

theorem Instance.bound (A : Instance (I:=I) (X:=X) (D:=D) Γ J) :
    A.regret ≤ A.rest+A.delay+(A.horizon:ℝ)*(A.delta+A.failure)+
      (A.influence*A.error/A.mincost)*(A.learnerCost+A.comparatorCost) := by
  have hg (m) : (∑ d, (A.episodes m d).budget) ≤ A.budget.G := by
    rw [A.generation_budget]
    exact uniform_budget (A.episodes m) A.delay A.horizon A.delta A.failure
      A.delta_nonneg A.failure_nonneg (A.delay_le m) (A.tasks_le m)
      (A.quality_le m) (A.miss_le m)
  have h := native_local Γ J A.KA A.LA A.KC A.LC A.score A.initial A.horizon
    A.influence A.error A.mincost A.learnerCost A.comparatorCost
    A.influence_nonneg A.error_nonneg A.mincost_pos A.learnerLocal A.comparatorLocal
    A.experiment A.budget A.remainder A.episodes A.endpoint hg A.zeroA A.zeroC
    A.rate A.code A.rate_eq A.code_eq A.learner_endpoint A.comparator_endpoint
  change A.regret ≤ _ at h
  dsimp [Instance.rest]
  rw [A.generation_budget]
  convert h using 1 <;> ring

/-- The no-regret endpoint invokes the actual native instance theorem. The
rate assumptions concern local quality, attempts, resources, and the other
explicit reference budgets, not the desired regret or generation gap. -/
theorem no_regret (A : ℕ → Instance (I:=I) (X:=X) (D:=D) Γ J)
    (rho k : ℝ) (attempts : ℕ → ℕ) (hr : 0 < rho) (hr1 : rho ≤ 1)
    (he : ∀ n, (A n).failure = (1-rho)^attempts n)
    (hk : ∀ n, (A n).influence*(A n).error/(A n).mincost = k)
    (hu : Tendsto (fun n => (A n).rest/(A n).horizon) atTop (𝓝 0))
    (hd : Tendsto (fun n => (A n).delay/(A n).horizon) atTop (𝓝 0))
    (hq : Tendsto (fun n => (A n).delta) atTop (𝓝 0))
    (hn : Tendsto attempts atTop atTop)
    (ha : Tendsto (fun n => (A n).learnerCost/(A n).horizon) atTop (𝓝 0))
    (hc : Tendsto (fun n => (A n).comparatorCost/(A n).horizon) atTop (𝓝 0)) :
    Tendsto (fun n => max 0 ((A n).regret/(A n).horizon)) atTop (𝓝 0) := by
  apply local_rate (fun n => (A n).regret) (fun n => (A n).rest)
    (fun n => (A n).delay) (fun n => ((A n).horizon:ℝ)) (fun n => (A n).delta)
    (fun n => (A n).learnerCost) (fun n => (A n).comparatorCost)
    attempts rho k hr hr1 (fun n => Nat.cast_pos.mpr (A n).horizon_pos)
    _ hu hd hq hn ha hc
  intro n
  simpa [he n, hk n] using (A n).bound

end DRGPR.LocalNativeFamily
#print axioms DRGPR.LocalNativeFamily.Instance.bound
#print axioms DRGPR.LocalNativeFamily.no_regret
