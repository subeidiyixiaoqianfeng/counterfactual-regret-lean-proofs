import CompletedClock
import PaperV17Correspondence

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology
namespace DRGPR.CompletedNativeV19
open LocalGenerationCertificate LocalFeedbackStability FeedbackTrajectory CompletedClock
variable {I D : Type} [Fintype I] [Fintype D]
  {X : ℕ → Type} [∀ t, Fintype (X t)]
  {Ω : Type*} [MeasurableSpace Ω] {M : Type*} [Nonempty M]
  (Γ : M → Measure Ω) [∀ m, IsProbabilityMeasure (Γ m)]
  (J : M → Ω → ℕ → Type*) [∀ m ω r, Fintype (J m ω r)]

/-- Validated completed-task model. Score positions and actual task counts
are different clocks. All intermediate expected-score endpoints are integrable.
The experiment law and representation certificates remain explicit contracts. -/
structure Instance where
  KA : Dynamics X
  LA : Dynamics X
  KC : M → Dynamics X
  LC : M → Dynamics X
  score : (t : ℕ) → X (t+1) → ℝ
  score_nonneg : ∀ t s, 0 ≤ score t s
  score_le_one : ∀ t s, score t s ≤ 1
  initial : FiniteController.Dist (X 0)
  T : ℕ
  T_pos : 0 < T
  H : ℝ
  eps : ℝ
  cmin : ℝ
  BA : ℝ
  BC : ℝ
  H_nonneg : 0 ≤ H
  eps_nonneg : 0 ≤ eps
  cmin_pos : 0 < cmin
  BA_nonneg : 0 ≤ BA
  BC_nonneg : 0 ≤ BC
  learnerLocal : NativeRepairEndpoint.Side KA LA (padded score) initial (T+1) H eps cmin BA
  comparatorLocal : ∀ m, NativeRepairEndpoint.Side (KC m) (LC m)
    (padded score) initial (T+1) H eps cmin BC
  terminalA : ∀ s, learnerLocal.resource T s = 0
  terminalC : ∀ m s, (comparatorLocal m).resource T s = 0
  activityA_nonneg : ∀ t s, 0 ≤ learnerLocal.activity t s
  activityC_nonneg : ∀ m t s, 0 ≤ (comparatorLocal m).activity t s
  resourceA_nonneg : ∀ t s, 0 ≤ learnerLocal.resource t s
  resourceC_nonneg : ∀ m t s, 0 ≤ (comparatorLocal m).resource t s
  experiment : ∀ m, DependentTransfer.Experiment Ω (J m) (Γ m)
  budget : ModelMain.Budget
  task_clock : budget.T = T
  run_pos : 0 < budget.b
  remainder : ∀ m, Remainder (experiment m) budget
  refA_integrable : ∀ m, Integrable (remainder m).refA (Γ m)
  aligned_integrable : ∀ m, Integrable (remainder m).aligned (Γ m)
  clean_integrable : ∀ m, Integrable (remainder m).clean (Γ m)
  path_integrable : ∀ m, Integrable (remainder m).refPath (Γ m)
  refM_integrable : ∀ m, Integrable (remainder m).refM (Γ m)
  episodes : M → D → Episode I
  episode_identity : ∀ m, (experiment m).availableTotal-
    (∫ ω, (remainder m).aligned ω ∂(Γ m)) = ∑ d, (episodes m d).gap
  delay : ℝ
  delta : ℝ
  failure : ℝ
  delta_nonneg : 0 ≤ delta
  failure_nonneg : 0 ≤ failure
  delay_le : ∀ m, (∑ d, ((episodes m d).delay:ℝ)) ≤ delay
  tasks_le : ∀ m, (∑ d, ((episodes m d).tasks:ℝ)) ≤ T
  quality_le : ∀ m d, (episodes m d).delta ≤ delta
  miss_le : ∀ m d, (1-(episodes m d).rho)^(episodes m d).attempts ≤ failure
  generation_budget : budget.G = delay+T*(delta+failure)
  zeroA : budget.E_cpA = 0
  zeroC : budget.E_cpC = 0
  rate : ℝ
  code : ℝ
  rate_eq : ∀ m, (experiment m).η = rate
  code_eq : ∀ m, (experiment m).C = code
  learner_identity : ∀ m, (∫ ω, (remainder m).refA ω ∂(Γ m)) =
    completedExpected LA score initial T
  comparator_identity : ∀ m, (∫ ω, (remainder m).refM ω ∂(Γ m)) =
    completedExpected (LC m) score initial T

variable {Γ J}
def Instance.regret (A : Instance (I:=I) (X:=X) (D:=D) Γ J) : ℝ :=
  completedExpected A.KA A.score A.initial A.T -
    sInf (Set.range (fun m => completedExpected (A.KC m) A.score A.initial A.T))
def Instance.rest (A : Instance (I:=I) (X:=X) (D:=D) Γ J) : ℝ :=
  A.budget.bound A.rate A.code-A.budget.G

theorem Instance.bound (A : Instance (I:=I) (X:=X) (D:=D) Γ J) :
    A.regret ≤ A.rest+A.delay+A.T*(A.delta+A.failure)+
      (A.H*A.eps/A.cmin)*(A.BA+A.BC) := by
  have hg m : (∑ d, (A.episodes m d).budget) ≤ A.budget.G := by
    rw [A.generation_budget]
    exact uniform_budget (A.episodes m) A.delay A.T A.delta A.failure
      A.delta_nonneg A.failure_nonneg (A.delay_le m) (A.tasks_le m)
      (A.quality_le m) (A.miss_le m)
  have ha m : (∫ ω, (A.remainder m).refA ω ∂(Γ m)) =
      expected A.LA (padded A.score) A.initial (A.T+1) := by
    rw [A.learner_identity m, completed_clock]
  have hc m : (∫ ω, (A.remainder m).refM ω ∂(Γ m)) =
      expected (A.LC m) (padded A.score) A.initial (A.T+1) := by
    rw [A.comparator_identity m, completed_clock]
  have h := native_local Γ J A.KA A.LA A.KC A.LC (padded A.score) A.initial (A.T+1)
    A.H A.eps A.cmin A.BA A.BC A.H_nonneg A.eps_nonneg A.cmin_pos
    A.learnerLocal A.comparatorLocal A.experiment A.budget A.remainder A.episodes
    A.episode_identity hg A.zeroA A.zeroC A.rate A.code A.rate_eq A.code_eq ha hc
  simp only [← completed_clock] at h
  change A.regret ≤ _ at h
  dsimp [Instance.rest]
  rw [A.generation_budget]
  convert h using 1 <;> ring

theorem variable_family
    (I D : ℕ → Type) [∀ n, Fintype (I n)] [∀ n, Fintype (D n)]
    (X : ℕ → ℕ → Type) [∀ n t, Fintype (X n t)]
    (Γ : ℕ → M → Measure Ω) [∀ n m, IsProbabilityMeasure (Γ n m)]
    (J : ℕ → M → Ω → ℕ → Type*) [∀ n m ω r, Fintype (J n m ω r)]
    (A : (n : ℕ) → Instance (I:=I n) (D:=D n) (X:=X n) (Γ n) (J n))
    (rho κ : ℝ) (attempts : ℕ → ℕ) (hr : 0 < rho) (hr1 : rho ≤ 1)
    (he : ∀ n, (A n).failure = (1-rho)^attempts n)
    (hk : ∀ n, (A n).H*(A n).eps/(A n).cmin = κ)
    (hu : Tendsto (fun n => (A n).rest/(A n).T) atTop (𝓝 0))
    (hd : Tendsto (fun n => (A n).delay/(A n).T) atTop (𝓝 0))
    (hq : Tendsto (fun n => (A n).delta) atTop (𝓝 0))
    (hn : Tendsto attempts atTop atTop)
    (hb : Tendsto (fun n => ((A n).BA+(A n).BC)/(A n).T) atTop (𝓝 0)) :
    Tendsto (fun n => max 0 ((A n).regret/(A n).T)) atTop (𝓝 0) := by
  have hT n : (0:ℝ) < (A n).T := Nat.cast_pos.mpr (A n).T_pos
  apply NativeNoRegret.upper_no_regret (fun n => (A n).regret)
    (fun n => (A n).rest+(A n).delay+(A n).T*((A n).delta+(1-rho)^attempts n)+
      κ*((A n).BA+(A n).BC)) (fun n => ((A n).T:ℝ)) hT
  · intro n
    simpa only [he n, hk n] using (A n).bound
  · have hp := (tendsto_pow_atTop_nhds_zero_of_lt_one (sub_nonneg.mpr hr1)
      (show 1-rho < 1 by linarith)).comp hn
    have hz := ((hu.add hd).add (hq.add hp)).add (hb.const_mul κ)
    convert hz using 1 <;> try norm_num
    funext n
    dsimp
    field_simp [(hT n).ne']
    <;> ring

end DRGPR.CompletedNativeV19
#print axioms DRGPR.CompletedNativeV19.Instance.bound
#print axioms DRGPR.CompletedNativeV19.variable_family
