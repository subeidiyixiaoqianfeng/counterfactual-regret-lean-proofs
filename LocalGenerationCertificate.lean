import GenerationProcess
import NativeRepairEndpoint
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology
namespace DRGPR.LocalGenerationCertificate
open SupportedInformation

variable {I : Type} [Fintype I]

/-- The predicate concerns a validated, retained, comparator-suitable outcome.
It is an analysis predicate, not an oracle supplied to the generating algorithm. -/
def missed (good : (n : ℕ) → Hist I n → I → Bool) : (n : ℕ) → Hist I n → Bool
  | 0, _ => true
  | n+1, h => missed good n h.1 && !(good n h.1 h.2)

def failure (k : (n : ℕ) → Hist I n → I → ℝ)
    (good : (n : ℕ) → Hist I n → I → Bool) (n : ℕ) : ℝ :=
  ∑ h, pathLaw k n h * (if missed good n h then 1 else 0)

theorem failure_step (k : (n : ℕ) → Hist I n → I → ℝ)
    (good : (n : ℕ) → Hist I n → I → Bool)
    (hk : ∀ n h i, 0 ≤ k n h i) (rho : ℝ)
    (hazard : ∀ n h, missed good n h = true →
      (∑ i, k n h i * (if good n h i then 0 else 1)) ≤ 1-rho) (n : ℕ) :
    failure k good (n+1) ≤ (1-rho)*failure k good n := by
  unfold failure
  change (∑ h : Hist I n × I, (pathLaw k n h.1*k n h.1 h.2)*
    (if missed good n h.1 && !(good n h.1 h.2) then 1 else 0)) ≤ _
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro h _
  by_cases hm : missed good n h = true
  · simp only [hm, Bool.true_and, Bool.not_eq_true, if_true, mul_one]
    have he : (∑ i, (pathLaw k n h*k n h i)*
        (if !(good n h i) then (1:ℝ) else 0)) =
        pathLaw k n h * (∑ i, k n h i*(if good n h i then 0 else 1)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      cases hh : good n h i <;> simp [hh, mul_assoc]
    rw [he]
    nlinarith [pathLaw_nonneg k hk n h, hazard n h hm]
  · have hf : missed good n h = false := Bool.eq_false_iff.mpr hm
    simp [hf]

theorem failure_bound (k : (n : ℕ) → Hist I n → I → ℝ)
    (good : (n : ℕ) → Hist I n → I → Bool)
    (hk : ∀ n h i, 0 ≤ k n h i) (rho : ℝ) (hr : rho ≤ 1)
    (hazard : ∀ n h, missed good n h = true →
      (∑ i, k n h i * (if good n h i then 0 else 1)) ≤ 1-rho) :
    ∀ n, failure k good n ≤ (1-rho)^n := by
  intro n
  induction n with
  | zero => simp [failure, Hist, pathLaw, missed]
  | succ n ih =>
    have hh := mul_le_mul_of_nonneg_left ih (sub_nonneg.mpr hr)
    simpa [pow_succ, mul_comm] using le_trans (failure_step k good hk rho hazard n) hh

/-- Per-task comparison, not an assumed cumulative generation regret. -/
structure Episode (I : Type) [Fintype I] where
  kernel : (n : ℕ) → Hist I n → I → ℝ
  nonneg : ∀ n h i, 0 ≤ kernel n h i
  normalized : ∀ n h, ∑ i, kernel n h i = 1
  good : (n : ℕ) → Hist I n → I → Bool
  rho : ℝ
  rho_pos : 0 < rho
  rho_le : rho ≤ 1
  hazard : ∀ n h, missed good n h = true →
    (∑ i, kernel n h i*(if good n h i then 0 else 1)) ≤ 1-rho
  attempts : ℕ
  delay : ℕ
  tasks : ℕ
  delta : ℝ
  delta_nonneg : 0 ≤ delta
  pre : Fin delay → Hist I attempts → ℝ
  post : Fin tasks → Hist I attempts → ℝ
  pre_le : ∀ t h, pre t h ≤ 1
  post_le : ∀ t h, post t h ≤ delta + (if missed good attempts h then 1 else 0)

def Episode.gap (E : Episode I) : ℝ :=
  ∑ h, pathLaw E.kernel E.attempts h * ((∑ t, E.pre t h)+(∑ t, E.post t h))

def Episode.budget (E : Episode I) : ℝ :=
  (E.delay:ℝ)+(E.tasks:ℝ)*(E.delta+(1-E.rho)^E.attempts)

theorem Episode.gap_le (E : Episode I) : E.gap ≤ E.budget := by
  have hp (h : Hist I E.attempts) : (∑ t, E.pre t h) ≤ (E.delay:ℝ) := by
    simpa using Finset.sum_le_sum (fun t (_ : t ∈ (Finset.univ : Finset (Fin E.delay))) => E.pre_le t h)
  have hq (h : Hist I E.attempts) : (∑ t, E.post t h) ≤
      (E.tasks:ℝ)*(E.delta+(if missed E.good E.attempts h then 1 else 0)) := by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using
      Finset.sum_le_sum (fun t (_ : t ∈ (Finset.univ : Finset (Fin E.tasks))) => E.post_le t h)
  have hs := Finset.sum_le_sum (fun h (_ : h ∈ (Finset.univ : Finset (Hist I E.attempts))) =>
    mul_le_mul_of_nonneg_left (add_le_add (hp h) (hq h))
      (pathLaw_nonneg E.kernel E.nonneg E.attempts h))
  have he : (∑ h, pathLaw E.kernel E.attempts h *
      ((E.delay:ℝ)+(E.tasks:ℝ)*(E.delta+(if missed E.good E.attempts h then 1 else 0)))) =
      (E.delay:ℝ)+(E.tasks:ℝ)*E.delta+(E.tasks:ℝ)*failure E.kernel E.good E.attempts := by
    calc
      _ = (∑ h, pathLaw E.kernel E.attempts h)*
          ((E.delay:ℝ)+(E.tasks:ℝ)*E.delta)+
          (E.tasks:ℝ)*failure E.kernel E.good E.attempts := by
        unfold failure
        rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro h _
        ring
      _ = _ := by rw [pathLaw_normalized E.kernel E.normalized]; ring
  rw [he] at hs
  have hb := mul_le_mul_of_nonneg_left
    (failure_bound E.kernel E.good E.nonneg E.rho E.rho_le E.hazard E.attempts)
    (Nat.cast_nonneg E.tasks)
  dsimp [Episode.gap, Episode.budget]
  linarith

theorem total_gap {D : Type} [Fintype D] (E : D → Episode I) :
    (∑ d, (E d).gap) ≤ ∑ d, (E d).budget :=
  Finset.sum_le_sum (fun d _ => (E d).gap_le)

/-- Reference-side remainder, with generation and both deployment bounds
removed. Deployment is supplied only by the outer local-kernel theorem. -/
structure Remainder {Ω : Type*} [MeasurableSpace Ω]
    {J : Ω → ℕ → Type*} [∀ ω r, Fintype (J ω r)]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (E : DependentTransfer.Experiment Ω J μ) (B : ModelMain.Budget) where
  refA : Ω → ℝ
  aligned : Ω → ℝ
  clean : Ω → ℝ
  refPath : Ω → ℝ
  refM : Ω → ℝ
  acquisition : (∫ ω, refA ω ∂μ)-E.selectedTotal ≤ B.F+B.prefix+B.D_A
  alignment : (∫ ω, aligned ω ∂μ)-(∫ ω, clean ω ∂μ) ≤ (B.b:ℝ)*B.S
  response : (∫ ω, clean ω ∂μ)-(∫ ω, refPath ω ∂μ) ≤ (B.H:ℝ)*(B.S+1)+B.D_C
  representation : (∫ ω, refPath ω ∂μ)-(∫ ω, refM ω ∂μ) ≤ B.E_nf
  capacity : E.V ≤ (B.b:ℝ)*B.V

def Remainder.certify {Ω : Type*} [MeasurableSpace Ω]
    {J : Ω → ℕ → Type*} [∀ ω r, Fintype (J ω r)]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {E : DependentTransfer.Experiment Ω J μ} {B : ModelMain.Budget}
    (W : Remainder E B) {D : Type} [Fintype D] (Q : D → Episode I)
    (endpoint : E.availableTotal-(∫ ω, W.aligned ω ∂μ)=∑ d, (Q d).gap)
    (budget : (∑ d, (Q d).budget) ≤ B.G)
    (zeroA : B.E_cpA = 0) (zeroC : B.E_cpC = 0) : ModelMain.Certificates E B where
  realA := W.refA
  refA := W.refA
  aligned := W.aligned
  clean := W.clean
  refPath := W.refPath
  refM := W.refM
  realM := W.refM
  cpA := by rw [zeroA]; simp
  acquisition := W.acquisition
  generation := by rw [endpoint]; exact le_trans (total_gap Q) budget
  alignment := W.alignment
  response := W.response
  representation := W.representation
  cpC := by rw [zeroC]; simp
  capacity := W.capacity

theorem uniform_budget {D : Type} [Fintype D] (Q : D → Episode I)
    (delay tasks delta fail : ℝ) (hd : 0 ≤ delta) (hf : 0 ≤ fail)
    (hdelay : (∑ d, ((Q d).delay:ℝ)) ≤ delay)
    (htasks : (∑ d, ((Q d).tasks:ℝ)) ≤ tasks)
    (hdelta : ∀ d, (Q d).delta ≤ delta)
    (hfail : ∀ d, (1-(Q d).rho)^(Q d).attempts ≤ fail) :
    (∑ d, (Q d).budget) ≤ delay+tasks*(delta+fail) := by
  have hs := Finset.sum_le_sum (fun d (_ : d ∈ (Finset.univ : Finset D)) =>
    add_le_add_left (mul_le_mul_of_nonneg_left (add_le_add (hdelta d) (hfail d))
      (Nat.cast_nonneg (Q d).tasks)) ((Q d).delay:ℝ))
  have ht := mul_le_mul_of_nonneg_right htasks (add_nonneg hd hf)
  simp only [Episode.budget, Finset.sum_add_distrib, ← Finset.sum_mul] at hs
  simp only [Episode.budget, Finset.sum_add_distrib]
  linarith

/-- Combined endpoint. No generation or deployment total-gap premise occurs.
Other reference interfaces and exact semantic endpoint identities remain explicit. -/
theorem native_local
    {X : ℕ → Type} [∀ t, Fintype (X t)]
    {Ω : Type*} [MeasurableSpace Ω] {M : Type*} [Nonempty M]
    {D : Type} [Fintype D]
    (Γ : M → Measure Ω) [∀ m, IsProbabilityMeasure (Γ m)]
    (J : M → Ω → ℕ → Type*) [∀ m ω r, Fintype (J m ω r)]
    (KA LA : LocalFeedbackStability.Dynamics X)
    (KC LC : M → LocalFeedbackStability.Dynamics X)
    (c : (t : ℕ) → X t → ℝ) (p : FiniteController.Dist (X 0)) (T : ℕ)
    (H eps cmin BA BC : ℝ) (hH : 0 ≤ H) (he : 0 ≤ eps) (hc : 0 < cmin)
    (DA : NativeRepairEndpoint.Side KA LA c p T H eps cmin BA)
    (DC : ∀ m, NativeRepairEndpoint.Side (KC m) (LC m) c p T H eps cmin BC)
    (E : ∀ m, DependentTransfer.Experiment Ω (J m) (Γ m)) (B : ModelMain.Budget)
    (W : ∀ m, Remainder (E m) B) (Q : M → D → Episode I)
    (endpoint : ∀ m, (E m).availableTotal-(∫ ω, (W m).aligned ω ∂(Γ m)) =
      ∑ d, (Q m d).gap)
    (budget : ∀ m, (∑ d, (Q m d).budget) ≤ B.G)
    (zeroA : B.E_cpA = 0) (zeroC : B.E_cpC = 0)
    (η code : ℝ) (hη : ∀ m, (E m).η = η) (hcode : ∀ m, (E m).C = code)
    (hA : ∀ m, (∫ ω, (W m).refA ω ∂(Γ m)) = FeedbackTrajectory.expected LA c p T)
    (hC : ∀ m, (∫ ω, (W m).refM ω ∂(Γ m)) = FeedbackTrajectory.expected (LC m) c p T) :
    FeedbackTrajectory.expected KA c p T -
      sInf (Set.range (fun m => FeedbackTrajectory.expected (KC m) c p T)) ≤
      B.bound η code + H*eps*(BA+BC)/cmin := by
  exact NativeRepairEndpoint.counterfactual Γ J KA LA KC LC c p T H eps cmin BA BC
    hH he hc DA DC E B
    (fun m => (W m).certify (Q m) (endpoint m) (budget m) zeroA zeroC)
    η code hη hcode hA hC

theorem local_rate (R U delay T delta BA BC : ℕ → ℝ) (attempts : ℕ → ℕ)
    (rho k : ℝ) (hr : 0 < rho) (hr1 : rho ≤ 1)
    (hT : ∀ n, 0 < T n)
    (hpoint : ∀ n, R n ≤ U n+delay n+T n*(delta n+(1-rho)^attempts n)+k*(BA n+BC n))
    (hu : Tendsto (fun n => U n/T n) atTop (𝓝 0))
    (hd : Tendsto (fun n => delay n/T n) atTop (𝓝 0))
    (hq : Tendsto delta atTop (𝓝 0)) (hn : Tendsto attempts atTop atTop)
    (ha : Tendsto (fun n => BA n/T n) atTop (𝓝 0))
    (hc : Tendsto (fun n => BC n/T n) atTop (𝓝 0)) :
    Tendsto (fun n => max 0 (R n/T n)) atTop (𝓝 0) := by
  apply NativeNoRegret.upper_no_regret R _ T hT hpoint
  have hp := (tendsto_pow_atTop_nhds_zero_of_lt_one (sub_nonneg.mpr hr1)
    (show 1-rho < 1 by linarith)).comp hn
  have hz := ((hu.add hd).add (hq.add hp)).add ((ha.add hc).const_mul k)
  convert hz using 1 <;> try norm_num
  funext n
  dsimp
  field_simp [(hT n).ne']
  <;> ring

theorem local_no_regret (R U G DA DC T : ℕ → ℝ)
    (hT : ∀ n, 0 < T n) (hpoint : ∀ n, R n ≤ U n+G n+DA n+DC n)
    (hU : Tendsto (fun n => U n/T n) atTop (𝓝 0))
    (hG : Tendsto (fun n => G n/T n) atTop (𝓝 0))
    (hDA : Tendsto (fun n => DA n/T n) atTop (𝓝 0))
    (hDC : Tendsto (fun n => DC n/T n) atTop (𝓝 0)) :
    Tendsto (fun n => max 0 (R n/T n)) atTop (𝓝 0) := by
  apply NativeNoRegret.upper_no_regret R _ T hT hpoint
  have h := ((hU.add hG).add hDA).add hDC
  convert h using 1 <;> try norm_num
  funext n
  ring

end DRGPR.LocalGenerationCertificate
#print axioms DRGPR.LocalGenerationCertificate.failure_step
#print axioms DRGPR.LocalGenerationCertificate.failure_bound
#print axioms DRGPR.LocalGenerationCertificate.Episode.gap_le
#print axioms DRGPR.LocalGenerationCertificate.total_gap
#print axioms DRGPR.LocalGenerationCertificate.uniform_budget
#print axioms DRGPR.LocalGenerationCertificate.native_local
#print axioms DRGPR.LocalGenerationCertificate.local_rate
#print axioms DRGPR.LocalGenerationCertificate.local_no_regret
