import ConcreteReflection

/-! Repeated native growth with a genuinely fallible validator. The native
rule uses the latest accepted card, not the reference Bandit. -/
noncomputable section
open Filter
open scoped BigOperators Topology
namespace DRGPR.ImperfectGrowth
open SupportedInformation LocalGenerationCertificate

@[simp]
theorem fin21 : (2 : Fin 3) ≠ 1 := by decide
@[simp]
theorem fin02 : (0 : Fin 3) ≠ 2 := by decide
@[simp]
theorem fin12 : (1 : Fin 3) ≠ 2 := by decide
@[simp]
theorem fin20 : (2 : Fin 3) ≠ 0 := by decide
@[simp]
theorem fin2mk : (2 : Fin 3) = ⟨2, by decide⟩ := rfl

def beta (m : ℕ) : ℝ := (1/2:ℝ)^m
theorem beta_nonneg (m) : 0 ≤ beta m := by unfold beta; positivity
theorem beta_pos (m) : 0 < beta m := by unfold beta; positivity
theorem beta_le_one (m) : beta m ≤ 1 := by
  exact pow_le_one₀ (by norm_num) (by norm_num)

/-- 0 is correct and accepted, 1 incorrect and accepted, 2 rejected. -/
def weight (m : ℕ) (o : Fin 3) : ℝ :=
  if o = 0 then 1/2 else if o = 1 then beta m/2 else (1-beta m)/2
def kernel (m : ℕ) : (n : ℕ) → Hist (Fin 3) n → Fin 3 → ℝ :=
  fun _ _ o => weight m o
def good : (n : ℕ) → Hist (Fin 3) n → Fin 3 → Bool := fun _ _ o => decide (o=0)

theorem weight_nonneg (m) (o : Fin 3) : 0 ≤ weight m o := by
  have hb := beta_le_one m
  have hp := beta_nonneg m
  unfold weight
  split_ifs <;> linarith
theorem weight_sum (m) : ∑ o, weight m o = 1 := by
  norm_num [Fin.sum_univ_succ, weight]; ring
theorem law_nonneg (m n) (h : Hist (Fin 3) n) : 0 ≤ pathLaw (kernel m) n h :=
  pathLaw_nonneg _ (fun _ _ o => weight_nonneg m o) n h
theorem law_sum (m n) : ∑ h, pathLaw (kernel m) n h = 1 :=
  pathLaw_normalized _ (fun _ _ => weight_sum m) n

/-- m independent fair validation probes miss a bad program with probability beta. -/
theorem raw_validation (m) :
    failure ConcreteReflection.trial ConcreteReflection.valid m = beta m :=
  ConcreteReflection.failure_exact m

def error : (n : ℕ) → Hist (Fin 3) n → Bool
  | 0, _ => true
  | n+1, h => if h.2 = 0 then false else if h.2 = 1 then true else error n h.1
def score (n) (h : Hist (Fin 3) n) : ℝ := if error n h then 1 else 0
def expected (m n : ℕ) : ℝ := ∑ h, pathLaw (kernel m) n h * score n h

theorem score_bounds (n) (h : Hist (Fin 3) n) : 0 ≤ score n h ∧ score n h ≤ 1 := by
  unfold score; split <;> norm_num
theorem expected_nonneg (m n) : 0 ≤ expected m n := by
  exact Finset.sum_nonneg (fun h _ => mul_nonneg (law_nonneg m n h) (score_bounds n h).1)
theorem expected_le_one (m n) : expected m n ≤ 1 := by
  have hs := Finset.sum_le_sum (fun h (_ : h ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (score_bounds n h).2 (law_nonneg m n h))
  simpa [expected, law_sum] using hs
theorem step_mean (m n) (h : Hist (Fin 3) n) :
    (∑ o, weight m o * score (n+1) (h,o)) =
      beta m/2 + (1-beta m)/2*score n h := by
  norm_num [Fin.sum_univ_succ, weight, score, error]
theorem expected_zero (m) : expected m 0 = 1 := by
  simp [expected, Hist, pathLaw, score, error]
theorem expected_step (m n) : expected m (n+1) =
    beta m/2+(1-beta m)/2*expected m n := by
  calc
    _ = ∑ h : Hist (Fin 3) n, pathLaw (kernel m) n h *
      (∑ o, weight m o * score (n+1) (h,o)) := by
        simp [expected, Hist, pathLaw, kernel, Fintype.sum_prod_type,
          Finset.mul_sum, mul_assoc]
    _ = ∑ h, pathLaw (kernel m) n h *
      (beta m/2+(1-beta m)/2*score n h) := by simp_rw [step_mean]
    _ = (∑ h, pathLaw (kernel m) n h)*(beta m/2) +
      (1-beta m)/2*(∑ h, pathLaw (kernel m) n h*score n h) := by
        rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intros; ring
    _ = _ := by rw [law_sum]; simp [expected]

theorem expected_bound (m n) : expected m n ≤ (1/2:ℝ)^n+beta m := by
  induction n with
  | zero => rw [expected_zero]; have hb := beta_nonneg m; norm_num; linarith
  | succ n ih =>
    rw [expected_step, pow_succ]
    have hb := beta_nonneg m
    have hl := beta_le_one m
    have hh := mul_le_mul_of_nonneg_left ih (by linarith : 0 ≤ (1-beta m)/2)
    have hp : 0 ≤ (1/2:ℝ)^n := by positivity
    nlinarith [mul_nonneg hb hp, sq_nonneg (beta m)]

theorem clean_failure (m n) : failure (kernel m) good n = (1/2:ℝ)^n := by
  induction n with
  | zero => simp [LocalGenerationCertificate.failure, Hist, pathLaw, missed]
  | succ n ih =>
    have hs : failure (kernel m) good (n+1) = failure (kernel m) good n / 2 := by
      unfold LocalGenerationCertificate.failure
      change (∑ h : Hist (Fin 3) n × Fin 3,
        (pathLaw (kernel m) n h.1 * kernel m n h.1 h.2)*
        (if missed good n h.1 && !(good n h.1 h.2) then (1:ℝ) else 0)) = _
      rw [Fintype.sum_prod_type, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro h _
      cases hm : missed good n h <;>
        norm_num [Fin.sum_univ_succ, good, kernel, weight, hm] <;> ring
    rw [hs, ih, pow_succ]; ring

theorem clean_le_native (n) (h : Hist (Fin 3) n) :
    (if missed good n h then (1:ℝ) else 0) ≤ score n h := by
  induction n with
  | zero => simp [missed, score, error]
  | succ n ih =>
    rcases h with ⟨h,o⟩
    have hh := ih h
    fin_cases o <;> simp_all [missed, good, score, error] <;> split_ifs <;> norm_num

theorem deployment_gap (m n) :
    0 ≤ expected m n-failure (kernel m) good n ∧
    expected m n-failure (kernel m) good n ≤ beta m := by
  have hs := Finset.sum_le_sum (fun h (_ : h ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (clean_le_native n h) (law_nonneg m n h))
  constructor
  · exact sub_nonneg.mpr hs
  · rw [clean_failure]; linarith [expected_bound m n]

def count : (n : ℕ) → Hist (Fin 3) n → ℕ
  | 0, _ => 0
  | n+1, h => count n h.1 + if h.2 = 2 then 0 else 1
def births (m n : ℕ) : ℝ := ∑ h, pathLaw (kernel m) n h * (count n h:ℝ)
theorem birth_count (m n) : births m n = n*((1+beta m)/2) := by
  induction n with
  | zero => simp [births, Hist, pathLaw, count]
  | succ n ih =>
    have step (h : Hist (Fin 3) n) :
        (∑ o, weight m o * (count (n+1) (h,o):ℝ)) =
        (count n h:ℝ)+(1+beta m)/2 := by
      norm_num [Fin.sum_univ_succ, count, weight]; ring
    calc
      _ = ∑ h : Hist (Fin 3) n, pathLaw (kernel m) n h *
        (∑ o, weight m o * (count (n+1) (h,o):ℝ)) := by
          simp [births, Hist, pathLaw, kernel, Fintype.sum_prod_type,
            Finset.mul_sum, mul_assoc]
      _ = births m n + (∑ h, pathLaw (kernel m) n h)*((1+beta m)/2) := by
        simp_rw [step, mul_add, Finset.sum_add_distrib]
        rw [← Finset.sum_mul]; rfl
      _ = _ := by rw [ih, law_sum]; push_cast; ring

def task (k : ℕ) (h : Hist (Fin 3) k) (t : ℕ) : ℝ :=
  if t < k then 1 else score k h
theorem task_sum (k N) (h : Hist (Fin 3) k) :
    (∑ t ∈ Finset.range (k+N), task k h t) = k+N*score k h := by
  rw [Finset.sum_range_add]
  have hp : (∑ t ∈ Finset.range k, task k h t) = (k:ℝ) := by
    have he : ∀ t ∈ Finset.range k, task k h t = 1 := by
      intro t ht; simp [task, Finset.mem_range.mp ht]
    simp [Finset.sum_congr rfl he]
  rw [hp]; simp [task, mul_comm]

def native (m k N : ℕ) : ℝ :=
  ∑ h, pathLaw (kernel m) k h * (∑ t ∈ Finset.range (k+N), task k h t)
theorem execution_identity (m k N) : native m k N = k+N*expected m k := by
  simp_rw [native, task_sum, mul_add, Finset.sum_add_distrib]
  rw [← Finset.sum_mul, law_sum]
  simp only [one_mul]
  congr 1
  unfold expected; rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intros; ring

theorem native_bound (m k N) : native m k N ≤ k+N*((1/2:ℝ)^k+beta m) := by
  rw [execution_identity]
  exact add_le_add_left (mul_le_mul_of_nonneg_left (expected_bound m k) (Nat.cast_nonneg N)) _

/-- Reserve generation, m probes and one registration at initiation. -/
def prefixCost (m k r : ℕ) : ℕ := (m+2)*min r k
theorem prefix_budget (m k r : ℕ) : prefixCost m k r ≤ (m+2)*k := by
  exact Nat.mul_le_mul_left _ (Nat.min_le_right r k)

theorem finite_regret {C : Type*} [Nonempty C] (J : C → ℝ)
    (hJ : ∀ c, 0 ≤ J c) (m k N E : ℕ) :
    E*native m k N - sInf (Set.range J) ≤
      E*(k+N*((1/2:ℝ)^k+beta m)) := by
  have hi : 0 ≤ sInf (Set.range J) := by
    apply le_csInf (Set.range_nonempty J)
    rintro _ ⟨c,rfl⟩; exact hJ c
  have hh := mul_le_mul_of_nonneg_left (native_bound m k N) (Nat.cast_nonneg E)
  linarith

def nextIdentity (old : Option ℕ) (j : ℕ) (o : Fin 3) : Option ℕ :=
  if o = 2 then old else some j
theorem selection_blind (old : Option ℕ) (j : ℕ) :
    nextIdentity old j 0 = nextIdentity old j 1 := by simp [nextIdentity]

theorem useful_birth (m k) :
    (∑ h, pathLaw (kernel m) k h * (if missed good k h then (0:ℝ) else 1)) =
      1-(1/2:ℝ)^k := by
  have he (h : Hist (Fin 3) k) : (if missed good k h then (0:ℝ) else 1) =
      1-(if missed good k h then 1 else 0) := by cases missed good k h <;> norm_num
  simp_rw [he, mul_sub, mul_one, Finset.sum_sub_distrib]
  rw [law_sum]; rw [← clean_failure m k]; rfl

theorem nonzero_deployment (m) :
    expected m 2 - failure (kernel m) good 2 = beta m/4 ∧
    0 < expected m 2 - failure (kernel m) good 2 := by
  have he : expected m 2 - failure (kernel m) good 2 = beta m/4 := by
    rw [clean_failure]
    norm_num [expected_step, expected_zero]; ring
  exact ⟨he, by rw [he]; exact div_pos (beta_pos m) (by norm_num)⟩

/-- An episode is sampled after its task type becomes current. Retaining old
cards changes the registry but not the specified type-local native kernel. -/
def epochKernel (m k : ℕ) : (e : ℕ) → Hist (Hist (Fin 3) k) e → Hist (Fin 3) k → ℝ :=
  fun _ _ h => pathLaw (kernel m) k h
def accumulated {I : Type} (f : I → ℝ) : (E : ℕ) → Hist I E → ℝ
  | 0, _ => 0
  | E+1, h => accumulated f E h.1 + f h.2

theorem epoch_sum (m k E) : ∑ h, pathLaw (epochKernel m k) E h = 1 :=
  pathLaw_normalized _ (fun _ _ => law_sum m k) E
theorem epoch_expectation (m k) (f : Hist (Fin 3) k → ℝ) (E) :
    (∑ h, pathLaw (epochKernel m k) E h * accumulated f E h) =
      E*(∑ h, pathLaw (kernel m) k h*f h) := by
  induction E with
  | zero => simp [Hist, pathLaw, accumulated]
  | succ E ih =>
    have step (h : Hist (Hist (Fin 3) k) E) :
        (∑ u, pathLaw (kernel m) k u * (accumulated f E h+f u)) =
        accumulated f E h + ∑ u, pathLaw (kernel m) k u*f u := by
      simp_rw [mul_add, Finset.sum_add_distrib]
      rw [← Finset.sum_mul, law_sum, one_mul]
    calc
      _ = ∑ h : Hist (Hist (Fin 3) k) E, pathLaw (epochKernel m k) E h *
        (∑ u, pathLaw (kernel m) k u * (accumulated f E h+f u)) := by
          simp [Hist, pathLaw, epochKernel, accumulated, Fintype.sum_prod_type,
            Finset.mul_sum, mul_assoc]
      _ = (∑ h, pathLaw (epochKernel m k) E h * accumulated f E h) +
        (∑ h, pathLaw (epochKernel m k) E h) *
        (∑ u, pathLaw (kernel m) k u * f u) := by
          simp_rw [step, mul_add, Finset.sum_add_distrib]
          rw [← Finset.sum_mul]
      _ = _ := by rw [ih, epoch_sum]; push_cast; ring

def fullNative (m k N E : ℕ) : ℝ :=
  ∑ h, pathLaw (epochKernel m k) E h *
    accumulated (fun u => ∑ t ∈ Finset.range (k+N), task k u t) E h
theorem full_execution (m k N E) : fullNative m k N E = E*native m k N :=
  epoch_expectation m k _ E

theorem full_prefix (m k E : ℕ) (r : Fin E → ℕ) :
    (∑ e, prefixCost m k (r e)) ≤ E*k*(m+2) := by
  have hh := Finset.sum_le_sum (fun e (_ : e ∈ Finset.univ) => prefix_budget m k (r e))
  simpa [mul_comm, mul_left_comm, mul_assoc] using hh

def cert (k N : ℕ) (h : Hist (Fin 3) k) : ModelMain.Budget where
  F := k
  G := ConcreteReflection.available (missed good k h) N
  D_A := 0
  D_C := 0
  E_nf := 0
  E_cpA := N*(score k h-(if missed good k h then 1 else 0))
  E_cpC := 0
  T := k+N
  b := 1
  H := 0
  N := 0
  S := 0
  V := 2*N

theorem conditional_transfer (k N : ℕ) (h : Hist (Fin 3) k) (η : ℝ) (hη : 0 < η)
    (j : ℝ) (hj : 0 ≤ j) :
    (k:ℝ)+N*score k h-j ≤ k+N*score k h+Real.log 2/η+η*N := by
  let failed := missed good k h
  let A := ConcreteReflection.reference failed η hη
  have hd := ConcreteReflection.dominates failed η hη N
  have hh := ModelMain.finite_controller_transfer A ConcreteReflection.best N (Real.log 2)
    (cert k N h)
    (by norm_num [A, ConcreteReflection.reference, ConcreteReflection.fair, ConcreteReflection.best])
    (by intros; simp [A, ConcreteReflection.reference, ConcreteReflection.best, ConcreteReflection.stay])
    (ConcreteReflection.code_bound failed η hη N)
    (by simpa [A, cert] using ConcreteReflection.capacity_bound failed η hη N)
    (k+N*score k h) (k+ConcreteReflection.available failed N)
    (ConcreteReflection.selected failed η hη N) (ConcreteReflection.available failed N)
    0 0 0 j j
    (ConcreteReflection.path_gap failed η hη N)
    (by cases he : missed good k h <;> simp [cert, failed, ConcreteReflection.available, he] <;> linarith)
    (by simpa [cert, ModelMain.Budget.prefix] using (sub_le_iff_le_add.mpr (by linarith :
      (k:ℝ)+ConcreteReflection.available failed N ≤ k+ConcreteReflection.selected failed η hη N)))
    (by simp [cert, failed]) (by simp [cert]) (by simp [cert])
    (by simpa [cert] using neg_nonpos.mpr hj) (by simp [cert])
  convert hh using 1 <;> cases he : missed good k h <;>
    simp [ModelMain.Budget.bound, ModelMain.Budget.delta, ModelMain.Budget.prefix,
      A, ConcreteReflection.reference, ConcreteReflection.available, cert, failed, he] <;> ring

theorem full_regret {C : Type*} [Nonempty C] (J : C → ℝ)
    (hJ : ∀ c, 0 ≤ J c) (m k N E : ℕ) :
    fullNative m k N E - sInf (Set.range J) ≤
      E*(k+N*((1/2:ℝ)^k+beta m)) := by
  rw [full_execution]
  exact finite_regret J hJ m k N E

theorem half_error (m k) (hm : 2 ≤ m) (hk : 2 ≤ k) : expected m k ≤ 1/2 := by
  have h1 := pow_le_pow_of_le_one (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num : (1/2:ℝ) ≤ 1) hm
  have h2 := pow_le_pow_of_le_one (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num : (1/2:ℝ) ≤ 1) hk
  have hh := expected_bound m k
  norm_num at h1 h2
  unfold beta at hh
  linarith

theorem no_reflection_linear {C : Type*} [Nonempty C] (J : C → ℝ)
    (hJ : ∀ c, 0 ≤ J c) (c : C) (m k N E : ℕ)
    (hm : 2 ≤ m) (hk : 2 ≤ k)
    (hc : J c = (E:ℝ)*(k+N)*expected m k) :
    (E:ℝ)*(k+N)/2 ≤ (E:ℝ)*(k+N)-sInf (Set.range J) := by
  have hl : BddBelow (Set.range J) := ⟨0, by rintro _ ⟨i,rfl⟩; exact hJ i⟩
  have hi := csInf_le hl (Set.mem_range_self c)
  have hs := mul_le_mul_of_nonneg_left (half_error m k hm hk)
    (by positivity : 0 ≤ (E:ℝ)*(k+N))
  rw [hc] at hi
  linarith

def K (n : ℕ) := n+2
def horizon (n : ℕ) := K n*(K n+(K n)^3)
def resources (n : ℕ) := (K n)^2*(K n+2)
def upper (n : ℕ) : ℝ := (K n:ℝ)*(K n+(K n:ℝ)^3*(2*beta (K n)))

theorem family_bound {C : Type*} [Nonempty C] (n) (J : C → ℝ)
    (hJ : ∀ c, 0 ≤ J c) :
    fullNative (K n) (K n) ((K n)^3) (K n)-sInf (Set.range J) ≤ upper n := by
  have hh := full_regret J hJ (K n) (K n) ((K n)^3) (K n)
  simpa [upper, beta, two_mul] using hh

theorem normalized_upper (n) :
    upper n/(horizon n:ℝ) ≤ 1/(K n:ℝ)^2+2*beta (K n) := by
  have hk : (0:ℝ) < K n := by simp [K]; positivity
  have hb := beta_nonneg (K n)
  have hT : (K n:ℝ)^4 ≤ (horizon n:ℝ) := by
    simp only [horizon, Nat.cast_mul, Nat.cast_add, Nat.cast_pow]
    nlinarith [sq_nonneg (K n:ℝ)]
  calc
    _ ≤ upper n/(K n:ℝ)^4 :=
      div_le_div_of_nonneg_left (by unfold upper; positivity) (by positivity) hT
    _ = _ := by unfold upper; field_simp; ring

theorem normalized_resources (n) :
    (resources n:ℝ)/(horizon n:ℝ) ≤ 1/(K n:ℝ)+2/(K n:ℝ)^2 := by
  have hk : (0:ℝ) < K n := by simp [K]; positivity
  have hT : (K n:ℝ)^4 ≤ (horizon n:ℝ) := by
    simp only [horizon, Nat.cast_mul, Nat.cast_add, Nat.cast_pow]
    nlinarith [sq_nonneg (K n:ℝ)]
  calc
    _ ≤ (resources n:ℝ)/(K n:ℝ)^4 :=
      div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity) hT
    _ = _ := by simp only [resources, Nat.cast_mul, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat]; field_simp; ring

theorem no_regret {C : Type*} [Nonempty C] (J : ℕ → C → ℝ)
    (hJ : ∀ n c, 0 ≤ J n c) :
    Tendsto (fun n => max 0 ((fullNative (K n) (K n) ((K n)^3) (K n)-
      sInf (Set.range (J n)))/(horizon n:ℝ))) atTop (𝓝 0) := by
  have hn : Tendsto K atTop atTop := tendsto_atTop_mono (fun n => by simp [K]) tendsto_id
  have hk : Tendsto (fun n => (K n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hn
  have hi := tendsto_inv_atTop_zero.comp hk
  have hp := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num : (1/2:ℝ) < 1)).comp hn
  have hl : Tendsto (fun n => 1/(K n:ℝ)^2+2*beta (K n)) atTop (𝓝 0) := by
    simpa [beta, div_eq_mul_inv, inv_pow] using (hi.pow 2).add (hp.const_mul 2)
  apply squeeze_zero (fun _ => le_max_left _ _) _ hl
  intro n
  apply max_le (by have hb := beta_nonneg (K n); positivity)
  exact le_trans (div_le_div_of_nonneg_right (family_bound n (J n) (hJ n))
    (Nat.cast_nonneg _)) (normalized_upper n)

theorem sublinear_resources :
    Tendsto (fun n => (resources n:ℝ)/(horizon n:ℝ)) atTop (𝓝 0) := by
  have hn : Tendsto K atTop atTop := tendsto_atTop_mono (fun n => by simp [K]) tendsto_id
  have hk : Tendsto (fun n => (K n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hn
  have hi := tendsto_inv_atTop_zero.comp hk
  have hl : Tendsto (fun n => 1/(K n:ℝ)+2/(K n:ℝ)^2) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv, inv_pow] using hi.add ((hi.pow 2).const_mul 2)
  exact squeeze_zero (fun n => by positivity) normalized_resources hl

def classify (m : ℕ) (isGood : Bool) (v : Hist Bool m) : Fin 3 :=
  if isGood then 0 else if missed ConcreteReflection.valid m v then 1 else 2
def rawWeight (m : ℕ) (o : Fin 3) : ℝ :=
  ∑ v, pathLaw ConcreteReflection.trial m v *
    (∑ b : Bool, (1/2:ℝ)*(if classify m b v = o then 1 else 0))

theorem raw_split (m) (v : Hist Bool m) (o : Fin 3) :
    (∑ b : Bool, (1/2:ℝ)*(if classify m b v = o then 1 else 0)) =
    if o=0 then 1/2 else if o=1 then ConcreteReflection.miss m v/2
      else (1-ConcreteReflection.miss m v)/2 := by
  fin_cases o <;> cases hv : missed ConcreteReflection.valid m v <;>
    norm_num [classify, Fintype.sum_bool, ConcreteReflection.miss, hv] <;> decide

theorem raw_embedding (m) (o : Fin 3) : rawWeight m o = weight m o := by
  have hn := pathLaw_normalized ConcreteReflection.trial ConcreteReflection.trial_normalized m
  have hf : (∑ v, pathLaw ConcreteReflection.trial m v * ConcreteReflection.miss m v) = beta m :=
    raw_validation m
  unfold rawWeight
  simp_rw [raw_split]
  fin_cases o
  · norm_num [weight, ← Finset.sum_mul, hn]
  · change (∑ v, pathLaw ConcreteReflection.trial m v*(ConcreteReflection.miss m v/2)) = beta m/2
    simp_rw [← mul_div_assoc, ← Finset.sum_div]
    rw [hf]
  · change (∑ v, pathLaw ConcreteReflection.trial m v*((1-ConcreteReflection.miss m v)/2)) = (1-beta m)/2
    simp_rw [← mul_div_assoc, mul_sub, mul_one, ← Finset.sum_div, Finset.sum_sub_distrib]
    rw [hn, hf]

theorem useful_growth_mean (m k E) :
    (∑ h, pathLaw (epochKernel m k) E h *
      accumulated (fun u => if missed good k u then (0:ℝ) else 1) E h) =
      E*(1-(1/2:ℝ)^k) := by
  rw [epoch_expectation, useful_birth]

def proactive (m k N E : ℕ) : ℝ :=
  ∑ h, pathLaw (epochKernel m k) E h *
    accumulated (fun u => (k+N:ℕ)*score k u) E h
theorem proactive_execution (m k N E) :
    proactive m k N E = (E:ℝ)*(k+N)*expected m k := by
  rw [proactive, epoch_expectation]
  have hh : (∑ h, pathLaw (kernel m) k h*((k+N:ℕ)*score k h)) =
      (k+N:ℕ)*expected m k := by
    unfold expected; rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intros; ring
  rw [hh]; push_cast; ring

def jointWeight (m k N : ℕ) (η : ℝ) (hη : 0 < η)
    (h : Hist (Fin 3) k) (g : Hist (Bool × Unit) N) : ℝ :=
  pathLaw (kernel m) k h *
    pathLaw (ConcreteReflection.reference (missed good k h) η hη).kernel N g
theorem reference_joint_law (m k N) (η : ℝ) (hη : 0 < η) :
    (∑ h, ∑ g, jointWeight m k N η hη h g) = 1 := by
  simp only [jointWeight, ← Finset.mul_sum, FiniteController.Program.law_normalized, mul_one]
  exact law_sum m k
theorem reference_native_marginal (m k N) (η : ℝ) (hη : 0 < η) :
    (∑ h, ∑ g, jointWeight m k N η hη h g *
      (∑ t ∈ Finset.range (k+N), task k h t)) = native m k N := by
  have he (h : Hist (Fin 3) k) :
      (∑ g, jointWeight m k N η hη h g*(∑ t ∈ Finset.range (k+N), task k h t)) =
      pathLaw (kernel m) k h*(∑ t ∈ Finset.range (k+N), task k h t) := by
    simp only [jointWeight, ← Finset.sum_mul, ← Finset.mul_sum,
      FiniteController.Program.law_normalized, mul_one]
  simp_rw [he]; rfl

def program (e : ℕ) (isGood : Bool) (tag x : ℕ) : ℕ :=
  if tag=e ∧ isGood=true then x else 0
theorem distinct_policies (e f : ℕ) (hef : e ≠ f) :
    program e true e 1 ≠ program f true e 1 := by simp [program, hef]
theorem deployment_score (e : ℕ) (isGood : Bool) :
    (if program e isGood e 1 = 1 then (0:ℝ) else 1) =
      if isGood then 0 else 1 := by cases isGood <;> norm_num [program]
def probePass (e : ℕ) (isGood probe : Bool) : Bool :=
  decide (program e isGood e (if probe then 1 else 0) = if probe then 1 else 0)
theorem probe_correct (e : ℕ) (isGood probe : Bool) :
    probePass e isGood probe = (isGood || !probe) := by
  cases isGood <;> cases probe <;> simp [probePass, program]
def allPass (e : ℕ) (isGood : Bool) : (m : ℕ) → Hist Bool m → Bool
  | 0, _ => true
  | m+1, h => allPass e isGood m h.1 && probePass e isGood h.2
theorem validator_correct (e) (isGood) (m) (h : Hist Bool m) :
    allPass e isGood m h = if isGood then true else missed ConcreteReflection.valid m h := by
  induction m with
  | zero => simp [allPass, missed]
  | succ m ih =>
    rw [allPass, ih h.1, probe_correct]
    cases isGood <;> simp [missed, ConcreteReflection.valid]

theorem count_le (k) (h : Hist (Fin 3) k) : count k h ≤ k := by
  induction k with
  | zero => simp [count]
  | succ k ih =>
    have hh := ih h.1
    simp only [count]
    split <;> omega
theorem actual_prefix (m k r u : ℕ) (hr : r ≤ k) (hu : u ≤ r) :
    (m+1)*r+u ≤ (m+2)*k := by
  calc
    _ ≤ (m+2)*r := by nlinarith
    _ ≤ _ := Nat.mul_le_mul_left _ hr

theorem mean_shift (m k) (f : Hist (Fin 3) k → ℝ) (c : ℝ) :
    (∑ h, pathLaw (kernel m) k h*(f h+c)) =
      (∑ h, pathLaw (kernel m) k h*f h)+c := by
  simp_rw [mul_add, Finset.sum_add_distrib]
  rw [← Finset.sum_mul, law_sum, one_mul]

theorem phase_transfer (m k N : ℕ) (η : ℝ) (hη : 0 < η) :
    native m k N ≤ k+N*((1/2:ℝ)^k+beta m)+Real.log 2/η+η*N := by
  have hs := Finset.sum_le_sum (fun h (_ : h ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (conditional_transfer k N h η hη 0 le_rfl) (law_nonneg m k h))
  simp only [sub_zero] at hs
  rw [mean_shift, mean_shift] at hs
  have he : (∑ h, pathLaw (kernel m) k h*((k:ℝ)+N*score k h)) = native m k N := by
    unfold native; simp_rw [task_sum]
  rw [he] at hs
  exact le_trans hs (add_le_add_right (add_le_add_right (native_bound m k N) _) _)

theorem full_transfer {C : Type*} [Nonempty C] (J : C → ℝ)
    (hJ : ∀ c, 0 ≤ J c) (m k N E : ℕ) (η : ℝ) (hη : 0 < η) :
    fullNative m k N E-sInf (Set.range J) ≤
      E*(k+N*((1/2:ℝ)^k+beta m)+Real.log 2/η+η*N) := by
  have hi : 0 ≤ sInf (Set.range J) := by
    apply le_csInf (Set.range_nonempty J)
    rintro _ ⟨c,rfl⟩; exact hJ c
  have hs := mul_le_mul_of_nonneg_left (phase_transfer m k N η hη) (Nat.cast_nonneg E)
  rw [full_execution]; linarith

theorem reference_terms_vanish :
    Tendsto (fun n => Real.log 2/(K n:ℝ)^2+1/(K n:ℝ)) atTop (𝓝 0) := by
  have hn : Tendsto K atTop atTop := tendsto_atTop_mono (fun n => by simp [K]) tendsto_id
  have hk : Tendsto (fun n => (K n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hn
  have hi := tendsto_inv_atTop_zero.comp hk
  simpa [div_eq_mul_inv, inv_pow] using ((hi.pow 2).const_mul (Real.log 2)).add hi

theorem useful_growth_unbounded :
    Tendsto (fun n => (K n:ℝ)*(1-(1/2:ℝ)^(K n))) atTop atTop := by
  have hn : Tendsto K atTop atTop := tendsto_atTop_mono (fun n => by simp [K]) tendsto_id
  have hk : Tendsto (fun n => (K n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hn
  have hl : Tendsto (fun n => (K n:ℝ)/2) atTop atTop := hk.atTop_div_const (by norm_num)
  apply tendsto_atTop_mono _ hl
  intro n
  have hp := pow_le_pow_of_le_one (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num : (1/2:ℝ) ≤ 1) (by simp [K] : 1 ≤ K n)
  norm_num at hp
  have hs := mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg (K n) : (0:ℝ) ≤ K n)
  nlinarith

/-- Explicit registry and native pointer. The hidden quality is stored as
program content, never consulted by the pointer update. Handles are local
attempt numbers, paired with the public phase number in the full system. -/
def pointer : (n : ℕ) → Hist (Fin 3) n → Option ℕ
  | 0, _ => none
  | n+1, h => nextIdentity (pointer n h.1) n h.2
def contentGood : (n : ℕ) → Hist (Fin 3) n → ℕ → Bool
  | 0, _, _ => false
  | n+1, h, i => if i=n then decide (h.2=0) else contentGood n h.1 i
def registered : (n : ℕ) → Hist (Fin 3) n → ℕ → Prop
  | 0, _, _ => False
  | n+1, h, i => (i=n ∧ h.2≠2) ∨ registered n h.1 i

theorem pointer_registered (n) (h : Hist (Fin 3) n) (i)
    (hi : pointer n h = some i) : i<n ∧ registered n h i := by
  induction n with
  | zero => simp [pointer] at hi
  | succ n ih =>
    simp only [pointer, nextIdentity] at hi
    by_cases ho : h.2=2
    · simp only [ho, if_pos] at hi
      have hh := ih h.1 hi
      exact ⟨by omega, Or.inr hh.2⟩
    · simp [ho] at hi
      subst i
      exact ⟨by omega, Or.inl ⟨rfl,ho⟩⟩

def selectedGood (n) (h : Hist (Fin 3) n) : Bool :=
  (pointer n h).elim false (contentGood n h)

theorem pointer_error (n) (h : Hist (Fin 3) n) :
    selectedGood n h = !(error n h) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases h with ⟨h,o⟩
    by_cases ho : o=2
    · subst o
      have he : selectedGood (n+1) (h,2) = selectedGood n h := by
        unfold selectedGood
        simp only [pointer, nextIdentity, if_pos rfl]
        cases hp : pointer n h with
        | none => rfl
        | some i =>
          have hb := (pointer_registered n h i hp).1
          simp [contentGood, Nat.ne_of_lt hb]
      rw [he, ih]
      simp [error]
    · simp only [selectedGood, pointer, nextIdentity, if_neg ho, Option.elim_some,
        contentGood, if_pos rfl]
      fin_cases o <;> simp_all [error]

theorem executed_task_score (e n) (h : Hist (Fin 3) n) :
    (if program e (selectedGood n h) e 1 = 1 then (0:ℝ) else 1) = score n h := by
  rw [deployment_score, pointer_error]
  cases he : error n h <;> simp [score, he]

theorem retained_correct_iff (n) (h : Hist (Fin 3) n) :
    (∃ i, i<n ∧ registered n h i ∧ contentGood n h i=true) ↔ missed good n h=false := by
  induction n with
  | zero => simp [registered, missed]
  | succ n ih =>
    rcases h with ⟨h,o⟩
    constructor
    · rintro ⟨i,hi,hr,hg⟩
      by_cases hin : i=n
      · subst i
        have ho : o=0 := by simpa [contentGood] using hg
        simp [missed, good, ho]
      · have hr' : registered n h i := by
          simpa [registered, hin] using hr
        have hg' : contentGood n h i=true := by
          simpa [contentGood, hin] using hg
        have hm := (ih h).mp ⟨i,by omega,hr',hg'⟩
        simp [missed, hm]
    · intro hm
      by_cases ho : o=0
      · refine ⟨n,by omega,Or.inl ⟨rfl,?_⟩,?_⟩
        · simp [ho]
        · simp [contentGood, ho]
      · have hm' : missed good n h=false := by simpa [missed, good, ho] using hm
        obtain ⟨i,hi,hr,hg⟩ := (ih h).mpr hm'
        refine ⟨i,by omega,Or.inr hr,?_⟩
        simp [contentGood, Nat.ne_of_lt hi, hg]

theorem completed_cost (m k) (h : Hist (Fin 3) k) :
    (m+1)*k+count k h ≤ (m+2)*k :=
  actual_prefix m k k (count k h) le_rfl (count_le k h)

theorem unfinished_cost (m k r g v a : ℕ) (hr : r≤k)
    (hg : g≤r) (hv : v≤m*r) (ha : a≤r) : g+v+a ≤ (m+2)*k := by
  have h : (m+2)*r ≤ (m+2)*k := Nat.mul_le_mul_left _ hr
  nlinarith

theorem variable_no_regret (C : ℕ → Type*) [∀ n, Nonempty (C n)]
    (J : (n : ℕ) → C n → ℝ) (hJ : ∀ n c, 0 ≤ J n c) :
    Tendsto (fun n => max 0 ((fullNative (K n) (K n) ((K n)^3) (K n)-
      sInf (Set.range (J n)))/(horizon n:ℝ))) atTop (𝓝 0) := by
  have hn : Tendsto K atTop atTop := tendsto_atTop_mono (fun n => by simp [K]) tendsto_id
  have hk : Tendsto (fun n => (K n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hn
  have hi := tendsto_inv_atTop_zero.comp hk
  have hp := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num : (1/2:ℝ) < 1)).comp hn
  have hl : Tendsto (fun n => 1/(K n:ℝ)^2+2*beta (K n)) atTop (𝓝 0) := by
    simpa [beta, div_eq_mul_inv, inv_pow] using (hi.pow 2).add (hp.const_mul 2)
  apply squeeze_zero (fun _ => le_max_left _ _) _ hl
  intro n
  apply max_le (by have hb := beta_nonneg (K n); positivity)
  exact le_trans (div_le_div_of_nonneg_right (family_bound n (J n) (hJ n))
    (Nat.cast_nonneg _)) (normalized_upper n)

/-- Scores evaluated on the actual program selected by the native pointer. -/
def actualTask (e k : ℕ) (h : Hist (Fin 3) k) (t : ℕ) : ℝ :=
  if t<k then (if program e false e 1=1 then 0 else 1)
  else (if program e (selectedGood k h) e 1=1 then 0 else 1)
theorem actual_task_identity (e k) (h : Hist (Fin 3) k) (t) :
    actualTask e k h t = task k h t := by
  by_cases ht : t<k
  · simp [actualTask, task, ht, program]
  · simpa only [actualTask, task, if_neg ht] using executed_task_score e k h

def actualTotal (k N : ℕ) : (E : ℕ) → Hist (Hist (Fin 3) k) E → ℝ
  | 0, _ => 0
  | E+1, h => actualTotal k N E h.1 +
      ∑ t ∈ Finset.range (k+N), actualTask E k h.2 t
theorem task_execution_identity (k N E) (h : Hist (Hist (Fin 3) k) E) :
    actualTotal k N E h =
      accumulated (fun u => ∑ t ∈ Finset.range (k+N), task k u t) E h := by
  induction E with
  | zero => rfl
  | succ E ih => simp only [actualTotal, accumulated, ih h.1, actual_task_identity]

def actualExpected (m k N E : ℕ) : ℝ :=
  ∑ h, pathLaw (epochKernel m k) E h * actualTotal k N E h
theorem actual_execution (m k N E) : actualExpected m k N E = fullNative m k N E := by
  simp only [actualExpected, task_execution_identity, fullNative]
theorem actual_regret {C : Type*} [Nonempty C] (J : C → ℝ)
    (hJ : ∀ c, 0 ≤ J c) (m k N E : ℕ) :
    actualExpected m k N E-sInf (Set.range J) ≤ E*(k+N*((1/2:ℝ)^k+beta m)) := by
  rw [actual_execution]
  exact full_regret J hJ m k N E
theorem actual_no_regret (C : ℕ → Type*) [∀ n, Nonempty (C n)]
    (J : (n : ℕ) → C n → ℝ) (hJ : ∀ n c, 0 ≤ J n c) :
    Tendsto (fun n => max 0 ((actualExpected (K n) (K n) ((K n)^3) (K n)-
      sInf (Set.range (J n)))/(horizon n:ℝ))) atTop (𝓝 0) := by
  simpa only [actual_execution] using variable_no_regret C J hJ

end DRGPR.ImperfectGrowth

#print axioms DRGPR.ImperfectGrowth.fin21
#print axioms DRGPR.ImperfectGrowth.fin02
#print axioms DRGPR.ImperfectGrowth.fin12
#print axioms DRGPR.ImperfectGrowth.fin20
#print axioms DRGPR.ImperfectGrowth.fin2mk
#print axioms DRGPR.ImperfectGrowth.beta_nonneg
#print axioms DRGPR.ImperfectGrowth.beta_pos
#print axioms DRGPR.ImperfectGrowth.beta_le_one
#print axioms DRGPR.ImperfectGrowth.weight_nonneg
#print axioms DRGPR.ImperfectGrowth.weight_sum
#print axioms DRGPR.ImperfectGrowth.law_nonneg
#print axioms DRGPR.ImperfectGrowth.law_sum
#print axioms DRGPR.ImperfectGrowth.raw_validation
#print axioms DRGPR.ImperfectGrowth.score_bounds
#print axioms DRGPR.ImperfectGrowth.expected_nonneg
#print axioms DRGPR.ImperfectGrowth.expected_le_one
#print axioms DRGPR.ImperfectGrowth.step_mean
#print axioms DRGPR.ImperfectGrowth.expected_zero
#print axioms DRGPR.ImperfectGrowth.expected_step
#print axioms DRGPR.ImperfectGrowth.expected_bound
#print axioms DRGPR.ImperfectGrowth.clean_failure
#print axioms DRGPR.ImperfectGrowth.clean_le_native
#print axioms DRGPR.ImperfectGrowth.deployment_gap
#print axioms DRGPR.ImperfectGrowth.birth_count
#print axioms DRGPR.ImperfectGrowth.task_sum
#print axioms DRGPR.ImperfectGrowth.execution_identity
#print axioms DRGPR.ImperfectGrowth.native_bound
#print axioms DRGPR.ImperfectGrowth.prefix_budget
#print axioms DRGPR.ImperfectGrowth.finite_regret
#print axioms DRGPR.ImperfectGrowth.selection_blind
#print axioms DRGPR.ImperfectGrowth.useful_birth
#print axioms DRGPR.ImperfectGrowth.nonzero_deployment
#print axioms DRGPR.ImperfectGrowth.epoch_sum
#print axioms DRGPR.ImperfectGrowth.epoch_expectation
#print axioms DRGPR.ImperfectGrowth.full_execution
#print axioms DRGPR.ImperfectGrowth.full_prefix
#print axioms DRGPR.ImperfectGrowth.conditional_transfer
#print axioms DRGPR.ImperfectGrowth.full_regret
#print axioms DRGPR.ImperfectGrowth.half_error
#print axioms DRGPR.ImperfectGrowth.no_reflection_linear
#print axioms DRGPR.ImperfectGrowth.family_bound
#print axioms DRGPR.ImperfectGrowth.normalized_upper
#print axioms DRGPR.ImperfectGrowth.normalized_resources
#print axioms DRGPR.ImperfectGrowth.no_regret
#print axioms DRGPR.ImperfectGrowth.sublinear_resources
#print axioms DRGPR.ImperfectGrowth.raw_split
#print axioms DRGPR.ImperfectGrowth.raw_embedding
#print axioms DRGPR.ImperfectGrowth.useful_growth_mean
#print axioms DRGPR.ImperfectGrowth.proactive_execution
#print axioms DRGPR.ImperfectGrowth.reference_joint_law
#print axioms DRGPR.ImperfectGrowth.reference_native_marginal
#print axioms DRGPR.ImperfectGrowth.distinct_policies
#print axioms DRGPR.ImperfectGrowth.deployment_score
#print axioms DRGPR.ImperfectGrowth.probe_correct
#print axioms DRGPR.ImperfectGrowth.validator_correct
#print axioms DRGPR.ImperfectGrowth.count_le
#print axioms DRGPR.ImperfectGrowth.actual_prefix
#print axioms DRGPR.ImperfectGrowth.mean_shift
#print axioms DRGPR.ImperfectGrowth.phase_transfer
#print axioms DRGPR.ImperfectGrowth.full_transfer
#print axioms DRGPR.ImperfectGrowth.reference_terms_vanish
#print axioms DRGPR.ImperfectGrowth.useful_growth_unbounded
#print axioms DRGPR.ImperfectGrowth.pointer_registered
#print axioms DRGPR.ImperfectGrowth.pointer_error
#print axioms DRGPR.ImperfectGrowth.executed_task_score
#print axioms DRGPR.ImperfectGrowth.retained_correct_iff
#print axioms DRGPR.ImperfectGrowth.completed_cost
#print axioms DRGPR.ImperfectGrowth.unfinished_cost
#print axioms DRGPR.ImperfectGrowth.variable_no_regret
#print axioms DRGPR.ImperfectGrowth.actual_task_identity
#print axioms DRGPR.ImperfectGrowth.task_execution_identity
#print axioms DRGPR.ImperfectGrowth.actual_execution
#print axioms DRGPR.ImperfectGrowth.actual_regret
#print axioms DRGPR.ImperfectGrowth.actual_no_regret
