import LocalGenerationCertificate
import ModelMain

/-! A concrete validation-dominant native reflector. No cumulative regret,
generation-gap or deployment-gap premise is used. The two-arm reference is
constructed, not run by the native controller. All failed trials are paid.
This is a horizon-indexed existence witness, not a universal LLM claim. -/
noncomputable section
open Filter
open scoped BigOperators Topology
namespace DRGPR.ConcreteReflection
open SupportedInformation FiniteController LocalGenerationCertificate

def trial : (n : ℕ) → Hist Bool n → Bool → ℝ := fun _ _ _ => 1/2
def valid : (n : ℕ) → Hist Bool n → Bool → Bool := fun _ _ b => b

theorem trial_nonneg : ∀ n h b, 0 ≤ trial n h b := by intros; norm_num [trial]
theorem trial_normalized : ∀ n h, ∑ b, trial n h b = 1 := by
  intros; norm_num [trial, Fintype.sum_bool]

def miss (k : ℕ) (h : Hist Bool k) : ℝ := if missed valid k h then 1 else 0
theorem miss_nonneg (k) (h : Hist Bool k) : 0 ≤ miss k h := by
  unfold miss; split <;> norm_num
theorem miss_le_one (k) (h : Hist Bool k) : miss k h ≤ 1 := by
  unfold miss; split <;> norm_num

theorem failure_exact (k : ℕ) : failure trial valid k = (1/2:ℝ)^k := by
  induction k with
  | zero => simp [LocalGenerationCertificate.failure, Hist, pathLaw, missed]
  | succ k ih =>
    have hs : failure trial valid (k+1) = failure trial valid k * (1/2:ℝ) := by
      unfold LocalGenerationCertificate.failure
      change (∑ h : Hist Bool k × Bool, (pathLaw trial k h.1*trial k h.1 h.2)*
        (if missed valid k h.1 && !(valid k h.1 h.2) then (1:ℝ) else 0)) = _
      rw [Fintype.sum_prod_type, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro h _
      cases hh : missed valid k h <;>
        simp [Fintype.sum_bool, valid, trial, hh]
    rw [hs, ih, pow_succ]

def episode (k N : ℕ) : Episode Bool where
  kernel := trial
  nonneg := trial_nonneg
  normalized := trial_normalized
  good := valid
  rho := 1/2
  rho_pos := by norm_num
  rho_le := by norm_num
  hazard := by intros; norm_num [trial, valid, Fintype.sum_bool]
  attempts := k
  delay := 0
  tasks := N
  delta := 0
  delta_nonneg := le_rfl
  pre := fun t => Fin.elim0 t
  post := fun _ h => miss k h
  pre_le := fun t => Fin.elim0 t
  post_le := by intros; simp [miss]

theorem generation_bound (k N : ℕ) :
    (∑ h, pathLaw trial k h * ((N:ℝ)*miss k h)) ≤ N*(1/2:ℝ)^k := by
  have hh := (episode k N).gap_le
  unfold Episode.gap Episode.budget at hh
  dsimp only [episode] at hh
  norm_num [Finset.sum_const, nsmul_eq_mul] at hh ⊢
  exact hh

/-- Immutable programs return x+1, x+2, and x. The third is absent until
validation. Boolean true refers to it after success and to x+2 after failure. -/
def output (id : Fin 3) (x : ℕ) : ℕ :=
  if id = 2 then x else x + id.val + 1
def identity (failed : Bool) (arm : Bool) : Fin 3 :=
  if arm then (if failed then 1 else 2) else 0
def taskLoss (failed arm : Bool) : ℝ := if arm && !failed then 0 else 1

theorem output_score (failed arm : Bool) (x : ℕ) :
    (if output (identity failed arm) x = x then (0:ℝ) else 1) =
      taskLoss failed arm := by
  cases failed <;> cases arm <;> simp [output, identity, taskLoss] <;> omega

theorem genuine_growth : identity false true = 2 ∧ identity true true = 1 ∧
    output 2 0 ≠ output 0 0 := by decide

def fair : FiniteController.Dist Bool where
  val := fun _ => 1/2
  nonneg := by intro; norm_num
  sum_one := by norm_num [Fintype.sum_bool]
def stay (i : Bool) : FiniteController.Dist Bool where
  val := fun j => if i = j then 1 else 0
  nonneg := by intro j; split <;> norm_num
  sum_one := by cases i <;> norm_num [Fintype.sum_bool]

def generator (guided : Bool) : FiniteController.Dist Bool :=
  if guided then stay true else fair
theorem same_frozen_generator (n) (h : Hist Bool n) (b : Bool) :
    (generator false).val b = trial n h b ∧
      (generator true).val true = 1 ∧ (generator true).val false = 0 := by
  simp [generator, fair, stay, trial]

def feedback (failed : Bool) : Feedback Bool Unit where
  kernel := fun _ _ => 1
  kernel_nonneg := by intros; norm_num
  kernel_sum := by intros; simp
  accepted := fun _ _ => true
  score := fun i _ => taskLoss failed i
  d := 1
  d_nonneg := by norm_num
  score_nonneg := by intro i o; unfold taskLoss; split <;> norm_num
  score_le := by intro i o; unfold taskLoss; split <;> norm_num
  q := fun _ => 1
  q_pos := by intros; norm_num
  q_def := by intros; simp
  loss := taskLoss failed
  moment := by intros; simp

def reference (failed : Bool) (η : ℝ) (hη : 0 < η) : Program Bool Unit where
  initial := fair
  feedback := fun _ _ => feedback failed
  transition := fun _ _ i => stay i
  η := η
  rate_pos := hη

def best : (n : ℕ) → Hist (Bool × Unit) n → Bool := fun _ _ => true

theorem code_bound (failed : Bool) (η : ℝ) (hη : 0 < η) (N : ℕ)
    (h : Hist (Bool × Unit) N) :
    -Real.log ((reference failed η hη).initial.val (best 0 ())) +
      cumulative ((reference failed η hη).codeIncrement best) N h ≤ Real.log 2 := by
  have hz : cumulative ((reference failed η hη).codeIncrement best) N h = 0 := by
    induction N with
    | zero => rfl
    | succ n ih =>
      rw [cumulative, ih h.1]
      simp [Program.codeIncrement, reference, best, stay]
  rw [hz]
  simp [reference, fair, best, Real.log_div]

theorem capacity_bound (failed : Bool) (η : ℝ) (hη : 0 < η) (N : ℕ) :
    (reference failed η hη).capacity N ≤ 2*N := by
  let A := reference failed η hη
  have hb n (h : Hist (Bool × Unit) n) : (A.round n h).burden ≤ 2 := by
    unfold RandomObservation.Round.burden
    have hh i : (if 0 < (A.round n h).p i then 1/(A.round n h).q i else 0) ≤ (1:ℝ) := by
      split <;> simp [A, Program.round, Feedback.round, reference, feedback]
    have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset Bool)) => hh i)
    simpa using hs
  have hs n : (∑ h, pathLaw A.kernel n h *
      ((A.feedback n h).d^2*(A.round n h).burden)) ≤ 2 := by
    calc
      _ ≤ ∑ h, pathLaw A.kernel n h*2 := by
        apply Finset.sum_le_sum
        intro h _
        apply mul_le_mul_of_nonneg_left _ (A.law_nonneg n h)
        simpa [A, reference, feedback] using hb n h
      _ = 2 := by rw [← Finset.sum_mul, A.law_normalized]; ring
  have hh := Finset.sum_le_sum (fun n (_ : n ∈ Finset.range N) => hs n)
  simpa [Program.capacity, A, mul_comm] using hh

def selected (failed : Bool) (η : ℝ) (hη : 0 < η) (N : ℕ) : ℝ :=
  ∑ h, pathLaw (reference failed η hη).kernel N h *
    cumulative (fun _ _ a => taskLoss failed a.1) N h
def available (failed : Bool) (N : ℕ) : ℝ := N*(if failed then 1 else 0)

theorem path_gap (failed : Bool) (η : ℝ) (hη : 0 < η) (N : ℕ) :
    selected failed η hη N - available failed N =
      ∑ h, pathLaw (reference failed η hη).kernel N h *
        cumulative ((reference failed η hη).actualGap best) N h := by
  have hc n (h : Hist (Bool × Unit) n) :
      cumulative ((reference failed η hη).actualGap best) n h =
      cumulative (fun _ _ a => taskLoss failed a.1) n h -
        n*(if failed then (1:ℝ) else 0) := by
    induction n with
    | zero => simp [cumulative]
    | succ n ih =>
      simp only [cumulative]
      rw [ih h.1]
      cases failed <;> simp [Program.actualGap, reference, feedback, best, taskLoss,
        Nat.cast_add, Nat.cast_one] <;> ring
  simp_rw [hc, mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, Program.law_normalized]
  simp [selected, available]

theorem dominates (failed : Bool) (η : ℝ) (hη : 0 < η) (N : ℕ) :
    available failed N ≤ selected failed η hη N := by
  have hc n (h : Hist (Bool × Unit) n) :
      n*(if failed then (1:ℝ) else 0) ≤
      cumulative (fun _ _ a => taskLoss failed a.1) n h := by
    induction n with
    | zero => simp [cumulative]
    | succ n ih =>
      have hi := ih h.1
      have ht : (if failed then (1:ℝ) else 0) ≤ taskLoss failed h.2.1 := by
        cases failed <;> cases h.2.1 <;> norm_num [taskLoss]
      simp only [cumulative, Nat.cast_add, Nat.cast_one]
      nlinarith
  have hs := Finset.sum_le_sum (fun h (_ : h ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (hc N h) ((reference failed η hη).law_nonneg N h))
  rw [← Finset.sum_mul, Program.law_normalized] at hs
  simpa [available, selected] using hs

/-- The native controller greedily uses a validated card, but on the first
post-commit task the implementation drops its output with probability 1/4.
That bit never changes memory or any later output. -/
def slip (b : Bool) : ℝ := if b then 1/4 else 3/4
def nativeConditional (k N : ℕ) (failed : Bool) : ℝ :=
  k + available failed N + (1/4)*(if failed then 0 else 1)
def comparator (k N : ℕ) (m : Bool) : ℝ := if m then 0 else k+N
def budget (k N : ℕ) (failed : Bool) : ModelMain.Budget where
  F := k
  G := available failed N
  D_A := 0
  D_C := 0
  E_nf := 0
  E_cpA := 1/4
  E_cpC := 0
  T := k+N
  b := 1
  H := 0
  N := 0
  S := 0
  V := 2*N

theorem conditional_main (k N : ℕ) (failed m : Bool) (η : ℝ) (hη : 0 < η) :
    nativeConditional k N failed - comparator k N m ≤
      k+available failed N+1/4+Real.log 2/η+η*N := by
  let A := reference failed η hη
  have hcmp : 0 ≤ comparator k N m := by cases m <;> simp [comparator]; positivity
  have hd := dominates failed η hη N
  have hh := ModelMain.finite_controller_transfer A best N (Real.log 2)
    (budget k N failed)
    (by norm_num [A, reference, fair, best])
    (by intros; simp [A, reference, best, stay])
    (code_bound failed η hη N)
    (by simpa [A, budget] using capacity_bound failed η hη N)
    (nativeConditional k N failed) (k+available failed N)
    (selected failed η hη N) (available failed N) 0 0 0
    (comparator k N m) (comparator k N m)
    (path_gap failed η hη N)
    (by cases failed <;> simp [nativeConditional, budget] <;> ring_nf <;> norm_num)
    (by simpa [budget, ModelMain.Budget.prefix] using (sub_le_iff_le_add.mpr (by linarith :
       (k:ℝ)+available failed N ≤ k+selected failed η hη N)))
    (by simp [budget]) (by simp [budget]) (by simp [budget])
    (by simpa [budget] using neg_nonpos.mpr hcmp) (by simp [budget])
  convert hh using 1 <;>
    simp [ModelMain.Budget.bound, ModelMain.Budget.delta, ModelMain.Budget.prefix,
      A, reference, budget] <;> ring

def nativeExpected (k N : ℕ) : ℝ :=
  ∑ h, pathLaw trial k h * nativeConditional k N (missed valid k h)
def regret (k N : ℕ) : ℝ := nativeExpected k N - sInf (Set.range (comparator k N))

def nativeTask (k : ℕ) (h : Hist Bool k) (b : Bool) (t : ℕ) : ℝ :=
  if t < k then 1 else miss k h + if t = k ∧ b = true then 1-miss k h else 0

theorem task_bounded (k) (h : Hist Bool k) (b : Bool) (t : ℕ) :
    0 ≤ nativeTask k h b t ∧ nativeTask k h b t ≤ 1 := by
  unfold nativeTask miss
  split_ifs <;> norm_num

theorem task_sum (k N : ℕ) (hN : 0 < N) (h : Hist Bool k) (b : Bool) :
    (∑ t ∈ Finset.range (k+N), nativeTask k h b t) =
      k+N*miss k h+(if b then 1-miss k h else 0) := by
  rw [Finset.sum_range_add]
  have hp : (∑ t ∈ Finset.range k, nativeTask k h b t) = (k:ℝ) := by
    have he : ∀ t ∈ Finset.range k, nativeTask k h b t = 1 := by
      intro t ht; simp [nativeTask, Finset.mem_range.mp ht]
    simp [Finset.sum_congr rfl he]
  rw [hp]
  have he t : nativeTask k h b (k+t) =
      miss k h + if t = 0 ∧ b = true then 1-miss k h else 0 := by
    simp [nativeTask]
  simp_rw [he, Finset.sum_add_distrib]
  cases b <;> simp [hN, Finset.sum_ite_eq', Nat.pos_iff_ne_zero] <;> ring

theorem slip_normalized : (∑ b, slip b) = 1 := by norm_num [slip, Fintype.sum_bool]
theorem slip_nonneg (b : Bool) : 0 ≤ slip b := by cases b <;> norm_num [slip]

theorem conditional_execution (k N : ℕ) (hN : 0 < N) (h : Hist Bool k) :
    (∑ b, slip b * ∑ t ∈ Finset.range (k+N), nativeTask k h b t) =
      nativeConditional k N (missed valid k h) := by
  simp_rw [task_sum k N hN]
  cases hh : missed valid k h <;>
    norm_num [Fintype.sum_bool, slip, nativeConditional, available, miss, hh] <;> ring

theorem execution_identity (k N : ℕ) (hN : 0 < N) :
    (∑ h, pathLaw trial k h *
      (∑ b, slip b * ∑ t ∈ Finset.range (k+N), nativeTask k h b t)) =
      nativeExpected k N := by
  simp_rw [conditional_execution k N hN]
  rfl

theorem full_law_normalized (k : ℕ) :
    (∑ h, ∑ b, pathLaw trial k h * slip b) = 1 := by
  simp_rw [← Finset.mul_sum, slip_normalized, mul_one]
  exact pathLaw_normalized trial trial_normalized k

/-- Couple native private noise to a fresh reference trajectory generated only
after the trial history is complete. Neither native marginal uses that path. -/
def jointWeight (k N : ℕ) (η : ℝ) (hη : 0 < η) (h : Hist Bool k)
    (d : Bool) (g : Hist (Bool × Unit) N) : ℝ :=
  pathLaw trial k h * slip d *
    pathLaw (reference (missed valid k h) η hη).kernel N g

theorem joint_law_normalized (k N : ℕ) (η : ℝ) (hη : 0 < η) :
    (∑ h, ∑ d, ∑ g, jointWeight k N η hη h d g) = 1 := by
  simp only [jointWeight, ← Finset.mul_sum, Program.law_normalized, mul_one]
  simpa only [← Finset.mul_sum] using full_law_normalized k

theorem native_marginal (k N : ℕ) (hN : 0 < N) (η : ℝ) (hη : 0 < η) :
    (∑ h, ∑ d, ∑ g, jointWeight k N η hη h d g *
      ∑ t ∈ Finset.range (k+N), nativeTask k h d t) = nativeExpected k N := by
  have inner (h : Hist Bool k) (d : Bool) :
      (∑ g, jointWeight k N η hη h d g * ∑ t ∈ Finset.range (k+N), nativeTask k h d t) =
        pathLaw trial k h * slip d * ∑ t ∈ Finset.range (k+N), nativeTask k h d t := by
    simp only [jointWeight, ← Finset.sum_mul, ← Finset.mul_sum,
      Program.law_normalized, mul_one]
  simp_rw [inner, mul_assoc, ← Finset.mul_sum]
  exact execution_identity k N hN

/-- Every completed trial costs one generation and one validation unit.
At most one new card and one deployment check are charged in addition. -/
def prefixCost (k r : ℕ) (registered checked : Bool) : ℕ :=
  2*min r k + (if registered then 1 else 0) + (if checked then 1 else 0)
theorem hard_prefix (k r : ℕ) (registered checked : Bool) :
    prefixCost k r registered checked ≤ 2*k+2 := by
  have hh := Nat.min_le_right r k
  cases registered <;> cases checked <;> simp [prefixCost] <;> omega
theorem comparator_hard (k : ℕ) (hk : 0 < k) : 3 ≤ 2*k+2 := by omega

def deployed (failed : Bool) : FiniteController.Dist Bool where
  val b := if failed then (if b then 1 else 0) else slip b
  nonneg := by intro b; cases failed <;> cases b <;> norm_num [slip]
  sum_one := by cases failed <;> norm_num [slip, Fintype.sum_bool]
def cleanOutput (failed : Bool) : FiniteController.Dist Bool := stay failed

theorem local_tv (failed : Bool) :
    FiniteTV.tv (deployed failed) (cleanOutput failed) =
      (1/4)*(if failed then 0 else 1) := by
  cases failed <;> norm_num [FiniteTV.tv, deployed, cleanOutput, stay, slip, Fintype.sum_bool]

theorem continuation_span (tail : ℝ) (a b : Bool) :
    |((if a then (1:ℝ) else 0)+tail)-((if b then 1 else 0)+tail)| ≤ 1 := by
  cases a <;> cases b <;> norm_num

theorem deployment_exact (k N : ℕ) (failed : Bool) :
    nativeConditional k N failed - (k+available failed N) =
      (1/4)*(if failed then 0 else 1) := by unfold nativeConditional; ring

theorem controllers_distinct : (deployed false).val true ≠ fair.val false := by
  norm_num [deployed, slip, fair]

def fullDeployment (failed : Bool) : FiniteController.Dist (Bool × Bool) where
  val s := if s.1 = failed then (deployed failed).val s.2 else 0
  nonneg := by intro s; split <;> simp [Dist.nonneg]
  sum_one := by
    cases failed <;> norm_num [Fintype.sum_prod_type, Fintype.sum_bool, deployed, slip]
def fullClean (failed : Bool) : FiniteController.Dist (Bool × Bool) where
  val s := if s.1 = failed then (cleanOutput failed).val s.2 else 0
  nonneg := by intro s; split <;> simp [Dist.nonneg]
  sum_one := by
    cases failed <;> norm_num [Fintype.sum_prod_type, Fintype.sum_bool, cleanOutput, stay]

theorem full_state_tv (failed : Bool) :
    FiniteTV.tv (fullDeployment failed) (fullClean failed) =
      (1/4)*(if failed then 0 else 1) := by
  cases failed <;> norm_num [FiniteTV.tv, fullDeployment, fullClean,
    deployed, cleanOutput, stay, slip, Fintype.sum_prod_type, Fintype.sum_bool]

theorem later_tasks_ignore_slip (k) (h : Hist Bool k) (t : ℕ) (ht : k < t) (a b : Bool) :
    nativeTask k h a t = nativeTask k h b t := by
  simp [nativeTask, show ¬t < k by omega, show t ≠ k by omega]

theorem comparator_inf (k N : ℕ) : sInf (Set.range (comparator k N)) = 0 := by
  apply le_antisymm
  · apply csInf_le
    · refine ⟨0, ?_⟩; rintro _ ⟨m,rfl⟩; cases m <;> simp [comparator]; positivity
    · exact ⟨true, by simp [comparator]⟩
  · apply le_csInf (Set.range_nonempty _)
    rintro _ ⟨m,rfl⟩; cases m <;> simp [comparator]; positivity

theorem no_reflection_linear (k N : ℕ) :
    comparator k N false - sInf (Set.range (comparator k N)) = (k+N:ℕ) := by
  rw [comparator_inf]
  change (k:ℝ)+N-0 = ((k+N:ℕ):ℝ)
  push_cast
  ring

theorem comparator_execution (k N : ℕ) (m : Bool) :
    (∑ _t ∈ Finset.range (k+N), if m then (0:ℝ) else 1) = comparator k N m := by
  cases m <;> simp [comparator]

theorem growth_positive (k : ℕ) (hk : 0 < k) :
    LocalGenerationCertificate.failure trial valid k < 1 := by
  rw [failure_exact]
  exact pow_lt_one₀ (by norm_num) (by norm_num) (Nat.ne_zero_of_lt hk)

theorem instantiated_bound (k N : ℕ) (η : ℝ) (hη : 0 < η) :
    regret k N ≤ k+N*(1/2:ℝ)^k+1/4+Real.log 2/η+η*N := by
  have hs := Finset.sum_le_sum (fun h (_ : h ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (conditional_main k N (missed valid k h) true η hη)
      (pathLaw_nonneg trial trial_nonneg k h))
  simp only [comparator, if_true, sub_zero] at hs
  have he : (∑ h, pathLaw trial k h *
      ((k:ℝ)+available (missed valid k h) N+1/4+Real.log 2/η+η*N)) =
      k+1/4+Real.log 2/η+η*N+∑ h, pathLaw trial k h*((N:ℝ)*miss k h) := by
    calc
      _ = (∑ h, pathLaw trial k h)*((k:ℝ)+1/4+Real.log 2/η+η*N)+
          ∑ h, pathLaw trial k h*((N:ℝ)*miss k h) := by
        rw [Finset.sum_mul, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro h _
        simp only [available, miss]
        ring
      _ = _ := by rw [pathLaw_normalized trial trial_normalized]; ring
  rw [he] at hs
  rw [regret, comparator_inf, sub_zero]
  change nativeExpected k N ≤ _
  have hg := generation_bound k N
  dsimp [nativeExpected]
  linarith

def K (n : ℕ) : ℕ := n+1
def horizon (n : ℕ) : ℕ := K n+(K n)^2
def familyRegret (n : ℕ) : ℝ := regret (K n) ((K n)^2)

theorem family_bound (n : ℕ) :
    familyRegret n ≤ (2+Real.log 2)*(K n)+(K n:ℝ)^2*(1/2:ℝ)^(K n)+1/4 := by
  have hk : (0:ℝ) < K n := by simp [K]; positivity
  have hh := instantiated_bound (K n) ((K n)^2) (1/(K n:ℝ)) (by positivity)
  dsimp [familyRegret]
  convert hh using 1 <;> push_cast <;> field_simp <;> ring

theorem nat_le_two_pow (k : ℕ) : (k:ℝ) ≤ (2:ℝ)^k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    have hp : (1:ℝ) ≤ (2:ℝ)^k := one_le_pow₀ (by norm_num)
    rw [Nat.cast_add, Nat.cast_one, pow_succ]
    linarith

theorem square_rate (n : ℕ) : familyRegret n ≤ (3+Real.log 2)*(K n)+1/4 := by
  have hk : (0:ℝ) ≤ K n := Nat.cast_nonneg _
  have hp : 0 < (2:ℝ)^(K n) := by positivity
  have hh : (K n:ℝ)*(1/2:ℝ)^(K n) ≤ 1 := by
    have he := div_le_one hp |>.mpr (nat_le_two_pow (K n))
    simpa [div_pow, div_eq_mul_inv] using he
  have hm := mul_le_mul_of_nonneg_left hh hk
  have hb := family_bound n
  nlinarith

theorem normalized_bound (n : ℕ) :
    familyRegret n/(horizon n:ℝ) ≤
      (2+Real.log 2)/(K n:ℝ)+(1/2:ℝ)^(K n)+(1/4)/(K n:ℝ)^2 := by
  have hk : (0:ℝ) < K n := by simp [K]; positivity
  have hc : 0 ≤ 2+Real.log 2 := by positivity
  have hT : (K n:ℝ)^2 ≤ (horizon n:ℝ) := by
    simp only [horizon, Nat.cast_add, Nat.cast_pow]; linarith
  have hTp : (0:ℝ) < horizon n := lt_of_lt_of_le (sq_pos_of_pos hk) hT
  calc
    _ ≤ ((2+Real.log 2)*(K n)+(K n:ℝ)^2*(1/2:ℝ)^(K n)+1/4)/(horizon n:ℝ) :=
      div_le_div_of_nonneg_right (family_bound n) hTp.le
    _ ≤ ((2+Real.log 2)*(K n)+(K n:ℝ)^2*(1/2:ℝ)^(K n)+1/4)/(K n:ℝ)^2 :=
      div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hk) hT
    _ = _ := by field_simp; ring

theorem no_regret :
    Tendsto (fun n => max 0 (familyRegret n/(horizon n:ℝ))) atTop (𝓝 0) := by
  have hkNat : Tendsto K atTop atTop := by
    exact tendsto_atTop_mono (fun n => by simp [K]) tendsto_id
  have hk : Tendsto (fun n => (K n:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hkNat
  have hi : Tendsto (fun n => (K n:ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hk
  have hpow : Tendsto (fun n => (1/2:ℝ)^(K n)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
      (by norm_num : (1/2:ℝ) < 1)).comp hkNat
  have hsum := ((hi.const_mul (2+Real.log 2)).add hpow).add ((hi.pow 2).const_mul (1/4))
  have hlim : Tendsto (fun n => (2+Real.log 2)/(K n:ℝ)+(1/2:ℝ)^(K n)+
      (1/4)/(K n:ℝ)^2) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv, inv_pow] using hsum
  apply squeeze_zero (fun _ => le_max_left _ _) _ hlim
  intro n
  apply max_le
  · positivity
  · exact normalized_bound n

end DRGPR.ConcreteReflection
#print axioms DRGPR.ConcreteReflection.generation_bound
#print axioms DRGPR.ConcreteReflection.failure_exact
#print axioms DRGPR.ConcreteReflection.execution_identity
#print axioms DRGPR.ConcreteReflection.hard_prefix
#print axioms DRGPR.ConcreteReflection.local_tv
#print axioms DRGPR.ConcreteReflection.full_state_tv
#print axioms DRGPR.ConcreteReflection.conditional_main
#print axioms DRGPR.ConcreteReflection.instantiated_bound
#print axioms DRGPR.ConcreteReflection.family_bound
#print axioms DRGPR.ConcreteReflection.square_rate
#print axioms DRGPR.ConcreteReflection.no_regret
#print axioms DRGPR.ConcreteReflection.trial_nonneg
#print axioms DRGPR.ConcreteReflection.trial_normalized
#print axioms DRGPR.ConcreteReflection.miss_nonneg
#print axioms DRGPR.ConcreteReflection.miss_le_one
#print axioms DRGPR.ConcreteReflection.output_score
#print axioms DRGPR.ConcreteReflection.genuine_growth
#print axioms DRGPR.ConcreteReflection.code_bound
#print axioms DRGPR.ConcreteReflection.capacity_bound
#print axioms DRGPR.ConcreteReflection.path_gap
#print axioms DRGPR.ConcreteReflection.dominates
#print axioms DRGPR.ConcreteReflection.task_bounded
#print axioms DRGPR.ConcreteReflection.task_sum
#print axioms DRGPR.ConcreteReflection.slip_normalized
#print axioms DRGPR.ConcreteReflection.slip_nonneg
#print axioms DRGPR.ConcreteReflection.conditional_execution
#print axioms DRGPR.ConcreteReflection.full_law_normalized
#print axioms DRGPR.ConcreteReflection.comparator_hard
#print axioms DRGPR.ConcreteReflection.continuation_span
#print axioms DRGPR.ConcreteReflection.deployment_exact
#print axioms DRGPR.ConcreteReflection.controllers_distinct
#print axioms DRGPR.ConcreteReflection.later_tasks_ignore_slip
#print axioms DRGPR.ConcreteReflection.comparator_inf
#print axioms DRGPR.ConcreteReflection.no_reflection_linear
#print axioms DRGPR.ConcreteReflection.nat_le_two_pow
#print axioms DRGPR.ConcreteReflection.normalized_bound
#print axioms DRGPR.ConcreteReflection.same_frozen_generator
#print axioms DRGPR.ConcreteReflection.comparator_execution
#print axioms DRGPR.ConcreteReflection.growth_positive
#print axioms DRGPR.ConcreteReflection.joint_law_normalized
#print axioms DRGPR.ConcreteReflection.native_marginal
