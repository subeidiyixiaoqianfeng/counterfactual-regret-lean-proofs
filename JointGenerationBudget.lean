import LocalGenerationCertificate
import NativeFamily
import ConcreteReflection
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology
namespace DRGPR.JointGenerationBudget
open LocalGenerationCertificate NativeSemantics

theorem geometric_exp (rho : ℝ) (hr : rho ≤ 1) (k : ℕ) :
    (1-rho)^k ≤ Real.exp (-(k:ℝ)*rho) := by
  have h : 1-rho ≤ Real.exp (-rho) := by
    linarith [Real.add_one_le_exp (-rho)]
  calc
    (1-rho)^k ≤ (Real.exp (-rho))^k := pow_le_pow_left₀ (sub_nonneg.mpr hr) h k
    _ = Real.exp (-(k:ℝ)*rho) := by rw [← Real.exp_nat_mul]; congr 1; ring

/-- Fixed design parameters shared across comparator witnesses. -/
structure Plan (D : Type) where
  attempts : D → ℕ
  delay : D → ℕ
  tasks : D → ℕ
  delta : D → ℝ
  rho : D → ℝ
  cost : D → ℝ
  delta_nonneg : ∀ e, 0 ≤ delta e
  rho_pos : ∀ e, 0 < rho e
  rho_le : ∀ e, rho e ≤ 1
  cost_nonneg : ∀ e, 0 ≤ cost e

variable {D I : Type} [Fintype D] [Fintype I]

def Plan.generation (P : Plan D) : ℝ :=
  ∑ e, ((P.delay e:ℝ)+(P.tasks e:ℝ)*
    (P.delta e+Real.exp (-(P.attempts e:ℝ)*P.rho e)))

def Plan.resource (P : Plan D) : ℝ := ∑ e, (P.attempts e:ℝ)*P.cost e

structure Match (P : Plan D) (Q : D → Episode I) : Prop where
  attempts : ∀ e, (Q e).attempts = P.attempts e
  delay : ∀ e, (Q e).delay ≤ P.delay e
  tasks : ∀ e, (Q e).tasks ≤ P.tasks e
  delta : ∀ e, (Q e).delta ≤ P.delta e
  rho : ∀ e, P.rho e ≤ (Q e).rho

theorem matched_budget (P : Plan D) (Q : D → Episode I) (H : Match P Q) :
    (∑ e, (Q e).budget) ≤ P.generation := by
  apply Finset.sum_le_sum
  intro e _
  have hf : (1-(Q e).rho)^(Q e).attempts ≤
      Real.exp (-(P.attempts e:ℝ)*P.rho e) := by
    rw [H.attempts e]
    apply le_trans (geometric_exp (Q e).rho (Q e).rho_le _)
    apply Real.exp_le_exp.mpr
    nlinarith [H.rho e, (Nat.cast_nonneg (P.attempts e) : (0:ℝ) ≤ P.attempts e)]
  have ht : ((Q e).tasks:ℝ) ≤ (P.tasks e:ℝ) := Nat.cast_le.mpr (H.tasks e)
  have hq := mul_le_mul ht (add_le_add (H.delta e) hf)
    (add_nonneg (Q e).delta_nonneg (pow_nonneg (sub_nonneg.mpr (Q e).rho_le) _))
    (Nat.cast_nonneg (P.tasks e))
  exact add_le_add (Nat.cast_le.mpr (H.delay e)) hq

/-- Prefix counts and prepaid cost envelopes imply a pathwise hard budget. -/
theorem hard_prefix (P : Plan D) (used : D → ℕ) (other spent budget : ℝ)
    (hu : ∀ e, used e ≤ P.attempts e)
    (hs : spent ≤ other+∑ e, (used e:ℝ)*P.cost e)
    (hb : other+P.resource ≤ budget) : spent ≤ budget := by
  have hsum : (∑ e, (used e:ℝ)*P.cost e) ≤ P.resource := by
    apply Finset.sum_le_sum
    intro e _
    exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (hu e)) (P.cost_nonneg e)
  linarith

variable {Ω : Type*} [MeasurableSpace Ω]
  {X : ℕ → Type*} [∀ t, MeasurableSpace (X t)] {T : ℕ}
  {J : Ω → ℕ → Type*} [∀ ω r, Fintype (J ω r)]
  {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- All original interfaces except generation. Deployment can be certified
directly or by the existing local resource theorem. There is no regret premise. -/
structure Interfaces (A C : Execution X T)
    (E : DependentTransfer.Experiment Ω J μ) (B : ModelMain.Budget) where
  learner : Realization A μ
  comparator : Realization C μ
  remainder : Remainder E B
  cpA : (∫ ω, learner.total ω ∂μ)-(∫ ω, remainder.refA ω ∂μ) ≤ B.E_cpA
  cpC : (∫ ω, remainder.refM ω ∂μ)-(∫ ω, comparator.total ω ∂μ) ≤ B.E_cpC
  horizon : B.T = T

def Interfaces.certify {A C : Execution X T}
    {E : DependentTransfer.Experiment Ω J μ} {B : ModelMain.Budget}
    (W : Interfaces A C E B) (P : Plan D) (Q : D → Episode I)
    (H : Match P Q)
    (endpoint : E.availableTotal-(∫ ω, W.remainder.aligned ω ∂μ)=∑ e, (Q e).gap)
    (hg : B.G = P.generation) : Witness A C E B where
  learner := W.learner
  comparator := W.comparator
  interfaces := {
    realA := W.learner.total
    realM := W.comparator.total
    refA := W.remainder.refA
    aligned := W.remainder.aligned
    clean := W.remainder.clean
    refPath := W.remainder.refPath
    refM := W.remainder.refM
    cpA := W.cpA
    cpC := W.cpC
    acquisition := W.remainder.acquisition
    alignment := W.remainder.alignment
    response := W.remainder.response
    representation := W.remainder.representation
    capacity := W.remainder.capacity
    generation := by rw [endpoint, hg]; exact (total_gap Q).trans (matched_budget P Q H) }
  realA_eq := rfl
  realM_eq := rfl
  horizon_eq := W.horizon

theorem native_joint {M : Type*} [Nonempty M]
    (Γ : M → Measure Ω) [∀ m, IsProbabilityMeasure (Γ m)]
    (J : M → Ω → ℕ → Type*) [∀ m ω r, Fintype (J m ω r)]
    (A : Execution X T) (C : M → Execution X T)
    (E : ∀ m, DependentTransfer.Experiment Ω (J m) (Γ m))
    (B : ModelMain.Budget) (eta code : ℝ)
    (W : ∀ m, Interfaces A (C m) (E m) B)
    (P : Plan D) (Q : M → D → Episode I) (H : ∀ m, Match P (Q m))
    (endpoint : ∀ m, (E m).availableTotal-
      (∫ ω, (W m).remainder.aligned ω ∂(Γ m))=∑ e, (Q m e).gap)
    (hg : B.G = P.generation)
    (hrate : ∀ m, (E m).η = eta) (hcode : ∀ m, (E m).C = code) :
    A.expectedLoss-sInf (Set.range (fun m => (C m).expectedLoss)) ≤
      (B.bound eta code-B.G)+P.generation := by
  have h := NativeFamily.own_coupling_counterfactual Γ J A C E B eta code
    (fun m => (W m).certify P (Q m) (H m) (endpoint m) hg) hrate hcode
  rw [hg]
  linarith

theorem uniform_generation (P : Plan D) (delay tasks delta exposure : ℝ)
    (hd : 0 ≤ delta)
    (hdelay : (∑ e, (P.delay e:ℝ)) ≤ delay)
    (htasks : (∑ e, (P.tasks e:ℝ)) ≤ tasks)
    (hdelta : ∀ e, P.delta e ≤ delta)
    (hexp : ∀ e, exposure ≤ (P.attempts e:ℝ)*P.rho e) :
    P.generation ≤ delay+tasks*(delta+Real.exp (-exposure)) := by
  have hs : P.generation ≤ (∑ e, (P.delay e:ℝ))+
      (∑ e, (P.tasks e:ℝ))*(delta+Real.exp (-exposure)) := by
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro e _
    have hf := Real.exp_le_exp.mpr (neg_le_neg (hexp e))
    exact add_le_add_left (mul_le_mul_of_nonneg_left (add_le_add (hdelta e)
      (by simpa [neg_mul] using hf)) (Nat.cast_nonneg (P.tasks e))) _
  have hm := mul_le_mul_of_nonneg_right htasks (add_nonneg hd (Real.exp_nonneg (-exposure)))
  linarith

theorem exposure_rate (R U delay T delta exposure : ℕ → ℝ)
    (hT : ∀ n, 0 < T n)
    (hpoint : ∀ n, R n ≤ U n+delay n+T n*(delta n+Real.exp (-exposure n)))
    (hu : Tendsto (fun n => (U n+delay n)/T n) atTop (𝓝 0))
    (hq : Tendsto delta atTop (𝓝 0))
    (hx : Tendsto exposure atTop atTop) :
    Tendsto (fun n => max 0 (R n/T n)) atTop (𝓝 0) := by
  apply NativeNoRegret.upper_no_regret R _ T hT hpoint
  have hf := Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hx)
  have h := hu.add (hq.add hf)
  convert h using 1 <;> try norm_num
  funext n
  dsimp
  field_simp [(hT n).ne']
  <;> ring

/-- Explicit trial quota with a log-failure target L. -/
def quota (L rho : ℝ) : ℕ := Nat.ceil (L/rho)

theorem quota_exposure (L rho : ℝ) (hr : 0 < rho) :
    L ≤ (quota L rho:ℝ)*rho := by
  exact (div_le_iff₀ hr).mp (Nat.le_ceil (L/rho))

theorem quota_cost (L rho c : ℝ) (hL : 0 ≤ L) (hr : 0 < rho) (hc : 0 ≤ c) :
    (quota L rho:ℝ)*c ≤ (L/rho+1)*c := by
  exact mul_le_mul_of_nonneg_right (Nat.ceil_lt_add_one (div_nonneg hL hr.le)).le hc

theorem quota_failure (L rho : ℝ) (hr : 0 < rho) (hr1 : rho ≤ 1) :
    (1-rho)^quota L rho ≤ Real.exp (-L) := by
  apply le_trans (geometric_exp rho hr1 _)
  apply Real.exp_le_exp.mpr
  simpa [neg_mul] using neg_le_neg (quota_exposure L rho hr)

/-- Horizon-dependent domains are allowed. The regret bound is derived from
native executions and episode witnesses before the asymptotic step. -/
theorem variable_family {M : Type*} [Nonempty M]
    (D I : ℕ → Type) [∀ n, Fintype (D n)] [∀ n, Fintype (I n)]
    (X : ℕ → ℕ → Type*) [∀ n t, MeasurableSpace (X n t)]
    (T : ℕ → ℕ) (hT : ∀ n, 0 < T n)
    (Γ : ℕ → M → Measure Ω) [∀ n m, IsProbabilityMeasure (Γ n m)]
    (J : ℕ → M → Ω → ℕ → Type*) [∀ n m ω r, Fintype (J n m ω r)]
    (A : ∀ n, Execution (X n) (T n)) (C : ∀ n, M → Execution (X n) (T n))
    (E : ∀ n m, DependentTransfer.Experiment Ω (J n m) (Γ n m))
    (B : ℕ → ModelMain.Budget) (eta code : ℕ → ℝ)
    (W : ∀ n m, Interfaces (A n) (C n m) (E n m) (B n))
    (P : ∀ n, Plan (D n)) (Q : ∀ n, M → D n → Episode (I n))
    (H : ∀ n m, Match (P n) (Q n m))
    (endpoint : ∀ n m, (E n m).availableTotal-
      (∫ ω, (W n m).remainder.aligned ω ∂(Γ n m))=∑ e, (Q n m e).gap)
    (hg : ∀ n, (B n).G = (P n).generation)
    (hrate : ∀ n m, (E n m).η = eta n) (hcode : ∀ n m, (E n m).C = code n)
    (delay delta exposure : ℕ → ℝ)
    (hdelta0 : ∀ n, 0 ≤ delta n)
    (hdelay : ∀ n, (∑ e, ((P n).delay e:ℝ)) ≤ delay n)
    (htasks : ∀ n, (∑ e, ((P n).tasks e:ℝ)) ≤ (T n:ℝ))
    (hdelta : ∀ n e, (P n).delta e ≤ delta n)
    (hexposure : ∀ n e, exposure n ≤ ((P n).attempts e:ℝ)*(P n).rho e)
    (hu : Tendsto (fun n => ((B n).bound (eta n) (code n)-(B n).G+delay n)/(T n:ℝ)) atTop (𝓝 0))
    (hq : Tendsto delta atTop (𝓝 0)) (hx : Tendsto exposure atTop atTop) :
    Tendsto (fun n => max 0
      (((A n).expectedLoss-sInf (Set.range (fun m => (C n m).expectedLoss)))/(T n:ℝ)))
      atTop (𝓝 0) := by
  apply exposure_rate _ (fun n => (B n).bound (eta n) (code n)-(B n).G)
    delay (fun n => (T n:ℝ)) delta exposure (fun n => Nat.cast_pos.mpr (hT n))
    _ hu hq hx
  intro n
  have hb := native_joint (Γ n) (J n) (A n) (C n) (E n) (B n) (eta n) (code n)
    (W n) (P n) (Q n) (H n) (endpoint n) (hg n) (hrate n) (hcode n)
  have he := uniform_generation (P n) (delay n) (T n) (delta n) (exposure n)
    (hdelta0 n) (hdelay n) (htasks n) (hdelta n) (hexposure n)
  dsimp only at ⊢
  linarith

theorem polynomial_cost (L a C delta : ℝ) (d s : ℕ)
    (hL : 0 ≤ L) (ha : 0 < a) (hC : 0 ≤ C)
    (hdelta : 0 < delta) (hdelta1 : delta ≤ 1) :
    (quota L (a*delta^d):ℝ)*(C/delta^s) ≤ C*(L/a+1)/delta^(d+s) := by
  have hx := pow_pos hdelta d
  have hy := pow_pos hdelta s
  have hx1 : delta^d ≤ 1 := pow_le_one₀ hdelta.le hdelta1
  apply (quota_cost L (a*delta^d) (C/delta^s) hL (mul_pos ha hx)
    (div_nonneg hC hy.le)).trans
  rw [pow_add]
  apply (le_div_iff₀ (mul_pos hx hy)).mpr
  have he : (L/(a*delta^d)+1)*(C/delta^s)*(delta^d*delta^s) = C*(L/a+delta^d) := by
    field_simp [ha.ne', hx.ne', hy.ne']
    <;> ring
  rw [he]
  exact mul_le_mul_of_nonneg_left (add_le_add_left hx1 _) hC

theorem polynomial_failure (L a delta : ℝ) (d : ℕ)
    (ha : 0 < a) (hdelta : 0 < delta) (hr1 : a*delta^d ≤ 1) :
    (1-a*delta^d)^quota L (a*delta^d) ≤ Real.exp (-L) :=
  quota_failure L (a*delta^d) (mul_pos ha (pow_pos hdelta d)) hr1

theorem log_failure (T : ℝ) (hT : 0 < T) :
    Real.exp (-(2*Real.log T)) = 1/T^2 := by
  rw [Real.exp_neg]
  have he : Real.exp (2*Real.log T) = T^2 := by
    simpa using Real.exp_nat_mul (Real.log T) 2
      |>.trans (by rw [Real.exp_log hT])
  rw [he]
  simp only [one_div]

theorem root_choice (z : ℝ) (p : ℕ) (hz : 0 < z) (hz1 : z ≤ 1) (hp : 0 < p) :
    0 < z ^ (1/(p:ℝ)) ∧ z ^ (1/(p:ℝ)) ≤ 1 ∧
      (z ^ (1/(p:ℝ))) ^ p = z := by
  have hpR : (0:ℝ) < p := Nat.cast_pos.mpr hp
  refine ⟨Real.rpow_pos_of_pos hz _, Real.rpow_le_one hz.le hz1 (by positivity), ?_⟩
  rw [← Real.rpow_natCast, ← Real.rpow_mul hz.le]
  simp [hpR.ne']

theorem root_rate (z : ℕ → ℝ) (p : ℕ) (hp : 0 < p)
    (hz : Tendsto z atTop (𝓝 0)) :
    Tendsto (fun n => (z n) ^ (1/(p:ℝ))) atTop (𝓝 0) := by
  have hpR : (0:ℝ) < p := Nat.cast_pos.mpr hp
  have h := (Real.continuous_rpow_const (show 0 ≤ (1/(p:ℝ)) by positivity)).tendsto 0
  have he := h.comp hz
  simpa only [Real.zero_rpow (show (1/(p:ℝ)) ≠ 0 by positivity)] using he

/-- The root choice, integer quota, cost and failure claims hold for the SAME
design. No independent minimization of the individual terms is performed. -/
theorem polynomial_allocation (E : ℕ) (L a C b : ℝ) (d s : ℕ)
    (hE : 0 < E) (hL : 0 ≤ L) (ha : 0 < a) (ha1 : a ≤ 1)
    (hC : 0 < C) (hb : 0 < b) (hp : 0 < d+s)
    (hz1 : C*(E:ℝ)*(L/a+1)/b ≤ 1) :
    let z := C*(E:ℝ)*(L/a+1)/b
    let delta := z ^ (1/((d+s:ℕ):ℝ))
    let k := quota L (a*delta^d)
    0 < delta ∧ delta ≤ 1 ∧
      (E:ℝ)*(k:ℝ)*(C/delta^s) ≤ b ∧
      (1-a*delta^d)^k ≤ Real.exp (-L) := by
  dsimp only
  let z := C*(E:ℝ)*(L/a+1)/b
  have hE' : (0:ℝ) < E := Nat.cast_pos.mpr hE
  have hratio : 0 < L/a+1 := by positivity
  have hz : 0 < z := by dsimp [z]; positivity
  obtain ⟨hd,hd1,hpow⟩ := root_choice z (d+s) hz hz1 hp
  refine ⟨hd,hd1,?_,?_⟩
  · have hc := polynomial_cost L a C (z ^ (1/((d+s:ℕ):ℝ))) d s hL ha hC.le hd hd1
    have hsum := mul_le_mul_of_nonneg_left hc hE'.le
    have he : (E:ℝ)*(C*(L/a+1)/(z ^ (1/((d+s:ℕ):ℝ)))^(d+s)) = b := by
      rw [hpow]
      rw [← mul_div_assoc]
      apply (div_eq_iff hz.ne').mpr
      dsimp [z]
      field_simp [hb.ne']
      <;> ring
    rw [he] at hsum
    simpa only [z, mul_assoc] using hsum
  · apply polynomial_failure L a (z ^ (1/((d+s:ℕ):ℝ))) d ha hd
    have hx : (z ^ (1/((d+s:ℕ):ℝ)))^d ≤ 1 := pow_le_one₀ hd.le hd1
    nlinarith

theorem polynomial_ratio_rate (E T b : ℕ → ℝ) (a C : ℝ)
    (hE : ∀ n, 0 ≤ E n) (hT : ∀ n, 2 ≤ T n) (hb : ∀ n, 0 < b n)
    (ha : 0 < a)
    (h : Tendsto (fun n => E n*Real.log (T n)/b n) atTop (𝓝 0)) :
    Tendsto (fun n => C*E n*(2*Real.log (T n)/a+1)/b n) atTop (𝓝 0) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hupper (n) : E n/b n ≤ (E n*Real.log (T n)/b n)/Real.log 2 := by
    apply (le_div_iff₀ hlog).mpr
    have hmono : Real.log 2 ≤ Real.log (T n) := Real.log_le_log (by norm_num) (hT n)
    have hh := mul_le_mul_of_nonneg_left hmono (div_nonneg (hE n) (hb n).le)
    convert hh using 1 <;> ring
  have hratio : Tendsto (fun n => E n/b n) atTop (𝓝 0) := by
    have hz := h.div_const (Real.log 2)
    simp only [zero_div] at hz
    exact squeeze_zero (fun n => div_nonneg (hE n) (hb n).le) hupper hz
  have hz := ((h.const_mul (2/a)).add hratio).const_mul C
  convert hz using 1 <;> try norm_num
  funext n
  dsimp
  field_simp [ha.ne', (hb n).ne']
  <;> ring

/-- Compatibility is checked on the old native regret and actual prefix-cost
functions, not on an unrelated abstract pair of scalar envelopes. -/
theorem concrete_compatibility (k N : ℕ) (eta : ℝ) (heta : 0 < eta) :
    (∀ r registered checked,
      ConcreteReflection.prefixCost k r registered checked ≤ 2*k+2) ∧
    ConcreteReflection.regret k N ≤
      k+N*Real.exp (-(k:ℝ)/2)+1/4+Real.log 2/eta+eta*N := by
  refine ⟨fun r registered checked => ConcreteReflection.hard_prefix k r registered checked, ?_⟩
  have hf := geometric_exp (1/2:ℝ) (by norm_num) k
  norm_num only [show (1-(1/2:ℝ)) = 1/2 by norm_num, mul_one_div] at hf
  have hm := mul_le_mul_of_nonneg_left hf (Nat.cast_nonneg N : (0:ℝ) ≤ N)
  have hb := ConcreteReflection.instantiated_bound k N eta heta
  linarith

end DRGPR.JointGenerationBudget
#print axioms DRGPR.JointGenerationBudget.geometric_exp
#print axioms DRGPR.JointGenerationBudget.matched_budget
#print axioms DRGPR.JointGenerationBudget.hard_prefix
#print axioms DRGPR.JointGenerationBudget.native_joint
#print axioms DRGPR.JointGenerationBudget.uniform_generation
#print axioms DRGPR.JointGenerationBudget.exposure_rate
#print axioms DRGPR.JointGenerationBudget.quota_exposure
#print axioms DRGPR.JointGenerationBudget.quota_cost
#print axioms DRGPR.JointGenerationBudget.quota_failure
#print axioms DRGPR.JointGenerationBudget.variable_family
#print axioms DRGPR.JointGenerationBudget.polynomial_cost
#print axioms DRGPR.JointGenerationBudget.polynomial_failure
#print axioms DRGPR.JointGenerationBudget.log_failure
#print axioms DRGPR.JointGenerationBudget.root_choice
#print axioms DRGPR.JointGenerationBudget.root_rate
#print axioms DRGPR.JointGenerationBudget.polynomial_allocation
#print axioms DRGPR.JointGenerationBudget.polynomial_ratio_rate
#print axioms DRGPR.JointGenerationBudget.concrete_compatibility
