import TableDistribution
import ObliviousFactorization
import ErasedProcess

noncomputable section
open scoped BigOperators
namespace DRGPR.ObliviousInformation
open SupportedInformation FiniteSimulation ErasedBandit TableDistribution
variable {I : Type} [Fintype I] [DecidableEq I]

abbrev Event (I : Type) := (I → Bool) × (I × Bool)
def params (e : ℝ) (j i : I) : ℝ := if i=j then 1/2-e else 1/2
def loss (b : Bool) : ℝ := if b then 0 else 1
def visible (x : Event I) : I × Option Bool :=
  (x.2.1,if x.2.2 then none else some (x.1 x.2.1))
def step (p : I → ℝ) (q e : ℝ) (j : I) (x : Event I) : ℝ :=
  row (params e j) x.1*(p x.2.1*bernoulli q x.2.2)
def regretStep (j : I) (x : Event I) : ℝ := loss (x.1 x.2.1)-loss (x.1 j)

def constantHistory {A : Type} (a : A) : (n : ℕ) → Hist A n
  | 0 => ()
  | n+1 => (constantHistory a n,a)

theorem step_normalized (p : I → ℝ) (q e : ℝ) (j : I) (hp : ∑ i, p i=1) :
    ∑ x, step p q e j x=1 := by
  unfold step
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum]
  have hi : (∑ a : I × Bool, p a.1*bernoulli q a.2)=1 := by
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum,bernoulli_normalized,mul_one]
    exact hp
  rw [hi]
  simpa using row_normalized (params e j)

theorem step_nonneg (p : I → ℝ) (q e : ℝ) (j : I)
    (hp : ∀ i, 0 ≤ p i) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (he : 0 ≤ e) (he1 : e ≤ 1/4) (x : Event I) : 0 ≤ step p q e j x := by
  apply mul_nonneg
  · exact row_nonneg _ (fun i => by unfold params; split_ifs <;> linarith)
      (fun i => by unfold params; split_ifs <;> linarith) _
  · apply mul_nonneg (hp _)
    cases x.2.2 <;> simp only [bernoulli] <;> linarith

theorem observable_step (p : I → ℝ) (q e : ℝ) (j : I) (a : I × Option Bool) :
    (∑ x, if visible x=a then step p q e j x else 0)=joint p q e j a := by
  obtain ⟨i,o⟩ := a
  cases o with
  | none =>
    have he : (∑ x, if visible x=(i,none) then step p q e j x else 0)=
        (∑ r, row (params e j) r)*(p i*(1-q)) := by
      simp [visible,step,Fintype.sum_prod_type,Fintype.sum_bool,bernoulli,Finset.sum_mul,mul_assoc]
    rw [he,row_normalized]
    simp [joint,FiniteInformation.erased]
  | some b =>
    have he : (∑ x, if visible x=(i,some b) then step p q e j x else 0)=
        (∑ r, if r i=b then row (params e j) r else 0)*(p i*q) := by
      simp [visible,step,Fintype.sum_prod_type,Fintype.sum_bool,bernoulli,Finset.sum_mul,mul_assoc,ite_and]
    rw [he,coordinate_marginal]
    simp only [joint,FiniteInformation.erased,params]
    ring

theorem conditional_regret (p : I → ℝ) (q e : ℝ) (j : I) (hp : ∑ i, p i=1) :
    (∑ x, step p q e j x*regretStep j x)=e*(1-p j) := by
  have hrow (i : I) : (∑ r, row (params e j) r*(loss (r i)-loss (r j)))=params e j i-params e j j := by
    change DRGPR.mean (row (params e j)) (fun r => loss (r i)-loss (r j))=_
    rw [DRGPR.mean_sub]
    exact congrArg₂ (·-·) (coordinate_loss (params e j) i) (coordinate_loss (params e j) j)
  have hmask (r : I → Bool) (i : I) :
      (∑ b, step p q e j (r,(i,b))*regretStep j (r,(i,b)))=
        p i*(row (params e j) r*(loss (r i)-loss (r j))) := by
    simp [step,regretStep,bernoulli,Fintype.sum_bool]
    ring
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type,hmask]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum,hrow]
  have he (i : I) : p i*(params e j i-params e j j)=e*p i-(if i=j then e*p i else 0) := by
    by_cases hi : i=j <;> simp [params,hi] <;> ring
  simp_rw [he]
  rw [Finset.sum_sub_distrib,← Finset.mul_sum,hp]
  simp
  ring

def kernel (p : (n : ℕ) → Hist (I × Option Bool) n → I → ℝ)
    (q e : ℝ) (j : I) (n : ℕ) (h : Hist (Event I) n) : Event I → ℝ :=
  step (p n (project visible n h)) q e j

theorem visible_law (p : (n : ℕ) → Hist (I × Option Bool) n → I → ℝ)
    (q e : ℝ) (j : I) (n : ℕ) (h : Hist (I × Option Bool) n) :
    (∑ g, if project visible n g=h then pathLaw (kernel p q e j) n g else 0)=
      pathLaw (fun t past => joint (p t past) q e j) n h := by
  exact projected_path_law visible _ _
    (fun t g a => observable_step (p t (project visible t g)) q e j a) n h

theorem expected_regret (p : (n : ℕ) → Hist (I × Option Bool) n → I → ℝ)
    (hp : ∀ n h, ∑ i, p n h i=1) (q e : ℝ) (j : I) (N : ℕ) :
    (∑ h, pathLaw (kernel p q e j) N h*cumulative (fun _ _ x => regretStep j x) N h)=
      e*((N:ℝ)-(∑ h, pathLaw (fun t h => joint (p t h) q e j) N h*counts j N h)) := by
  let k := fun t h => joint (p t h) q e j
  let l := kernel p q e j
  let c := fun (_t : ℕ) (_h : Hist (I × Option Bool) _t) (x : I × Option Bool) => e*(1-(if x.1=j then 1 else 0))
  have hls : ∀ t h, ∑ x, l t h x=1 := fun t h => step_normalized _ q e j (hp t (project visible t h))
  have hobs (t : ℕ) (h : Hist (Event I) t) :
      (∑ x, l t h x*c t (project visible t h) (visible x)) = e*(1-p t (project visible t h) j) := by
    have hproj := FiniteStochastic.pushforward_mean (l t h) visible
      (k t (project visible t h))
      (fun a => observable_step (p t (project visible t h)) q e j a)
      (c t (project visible t h))
    change (∑ x, l t h x*c t (project visible t h) (visible x)) = _ at hproj
    rw [hproj]
    change DRGPR.mean (k t (project visible t h)) (fun x => e*(1-(if x.1=j then 1 else 0)))=_
    rw [FiniteStochastic.mean_mul,DRGPR.mean_sub,
      DRGPR.mean_const _ (ErasedBandit.joint_normalized _ _ _ _ (hp t (project visible t h)))]
    rw [show DRGPR.mean (k t (project visible t h)) (fun x => if x.1=j then 1 else 0)=
      p t (project visible t h) j from by
        dsimp [DRGPR.mean,k]
        simp [joint,Fintype.sum_prod_type,mul_ite,← Finset.mul_sum,FiniteInformation.erased,bernoulli]
        <;> ring]
  have hh : (∑ h, pathLaw l N h*cumulative (fun _ _ x => regretStep j x) N h)=
      ∑ h, pathLaw l N h*cumulative (fun t h x => c t (project visible t h) (visible x)) N h := by
    rw [expected_cumulative _ _ hls,expected_cumulative _ _ hls]
    apply Finset.sum_congr rfl
    intro t _
    apply Finset.sum_congr rfl
    intro h _
    congr 1
    rw [hobs]
    exact conditional_regret _ q e j (hp t (project visible t h))
  rw [hh]
  simp_rw [cumulative_projection]
  rw [projected_expectation visible k l
    (fun t h a => observable_step (p t (project visible t h)) q e j a)]
  have hc : ∀ n h, cumulative c n h=e*((n:ℝ)-counts j n h) := by
    intro n
    induction n with
    | zero => intro h; simp [cumulative,counts]
    | succ n ih =>
      intro h
      change cumulative c n h.1+e*(1-(if h.2.1=j then 1 else 0)) = _
      rw [ih]
      simp only [counts,cumulative,Nat.cast_add,Nat.cast_one]
      ring
  simp_rw [hc]
  change DRGPR.mean (pathLaw k N) (fun h => e*((N:ℝ)-counts j N h)) = _
  rw [FiniteStochastic.mean_mul,DRGPR.mean_sub,
    DRGPR.mean_const _ (pathLaw_normalized k (fun t h => ErasedBandit.joint_normalized _ _ _ _ (hp t h)) N)]
  rfl

def choice (p : (n : ℕ) → Hist (I × Option Bool) n → I → ℝ) (q : ℝ)
    (n : ℕ) (table : Hist (I → Bool) n) (coins : Hist (I × Bool) n) (a : I × Bool) : ℝ :=
  p n (project visible n (ObliviousFactorization.zip n table coins)) a.1*bernoulli q a.2

def fixedRegret (p : (n : ℕ) → Hist (I × Option Bool) n → I → ℝ) (q : ℝ)
    (j : I) (N : ℕ) (table : Hist (I → Bool) N) : ℝ :=
  ∑ a, ObliviousFactorization.playerWeight (choice p q) N table a*
    cumulative (fun _ _ x => regretStep j x) N (ObliviousFactorization.zip N table a)

theorem fixed_player_normalized
    (p : (n : ℕ) → Hist (I × Option Bool) n → I → ℝ)
    (hp : ∀ n h, ∑ i, p n h i=1) (q : ℝ) (N : ℕ) (table : Hist (I → Bool) N) :
    ∑ a, ObliviousFactorization.playerWeight (choice p q) N table a=1 := by
  apply ObliviousFactorization.player_normalized
  intro n e h
  unfold choice
  rw [Fintype.sum_prod_type]
  simp only [← Finset.mul_sum,bernoulli_normalized,mul_one]
  exact hp _ _

theorem fixed_table_factorization
    (p : (n : ℕ) → Hist (I × Option Bool) n → I → ℝ)
    (q e : ℝ) (j : I) (N : ℕ) :
    (∑ h, pathLaw (kernel p q e j) N h*cumulative (fun _ _ x => regretStep j x) N h)=
      ∑ table, pathLaw (fun _ _ => row (params e j)) N table*fixedRegret p q j N table := by
  have hk : ObliviousFactorization.fullKernel (fun _ _ => row (params e j)) (choice p q)=kernel p q e j := by
    funext n h x
    simp [ObliviousFactorization.fullKernel,choice,kernel,step,ObliviousFactorization.zip_project]
  rw [← hk]
  exact ObliviousFactorization.expectation_factorization _ _ N _

/-- The non-erased table is fixed before play. Only one coordinate is observed,
with the independent logger retained inside the private-run expectation. -/
theorem exists_fixed_hard_table
    (p : (n : ℕ) → Hist (I × Option Bool) n → I → ℝ)
    (hp : ∀ n h i, 0 ≤ p n h i) (hp1 : ∀ n h, ∑ i, p n h i=1)
    (q : ℝ) (N : ℕ) (hN : 0 < N) (j₀ : I)
    (hK : (2:ℝ) ≤ Fintype.card I) (hq : 0 < q) (hq1 : q ≤ 1) :
    ∃ (j : I) (table : Hist (I → Bool) N),
      (1/32:ℝ)*min (N:ℝ) (Real.sqrt ((Fintype.card I)*N/q)) ≤ fixedRegret p q j N table := by
  let e := InformationRate.gap (Fintype.card I) q N
  let L := fun j => ∑ h, pathLaw (kernel p q e j) N h*cumulative (fun _ _ x => regretStep j x) N h
  have hK0 : (0:ℝ) < Fintype.card I := by linarith
  have hsum : (∑ j : I, (1/(Fintype.card I:ℝ)))=1 := by
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    field_simp
  have hmean : (∑ j, (1/(Fintype.card I:ℝ))*L j)=
      e*((N:ℝ)-(∑ j, ∑ h, pathLaw (fun t h => joint (p t h) q e j) N h*counts j N h)/(Fintype.card I:ℝ)) := by
    simp only [L,expected_regret p hp1,mul_sub,Finset.sum_sub_distrib]
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    rw [← Finset.mul_sum,← Finset.mul_sum]
    field_simp [hK0.ne']
    <;> ring
  have hl := FiniteBanditLower.single_phase p hp hp1 q N hN j₀ hK hq hq1
  dsimp only at hl
  have ha : (1/32:ℝ)*min (N:ℝ) (Real.sqrt ((Fintype.card I)*N/q)) ≤
      ∑ j, (1/(Fintype.card I:ℝ))*L j := by rw [hmean]; exact hl
  letI : Nonempty I := ⟨j₀⟩
  obtain ⟨j,hj⟩ := ObliviousFactorization.fixed_instance_from_average
    (fun _ : I => 1/(Fintype.card I:ℝ)) L (fun _ => by positivity) hsum _ ha
  have he := InformationRate.gap_properties (Fintype.card I) q N hK0 hq (Nat.cast_pos.mpr hN)
  have hpR : ∀ i, 0 ≤ params e j i := fun i => by unfold params; split_ifs <;> linarith [he.1,he.2.1]
  have hpR1 : ∀ i, params e j i ≤ 1 := fun i => by unfold params; split_ifs <;> linarith [he.1,he.2.1]
  have envNonneg := pathLaw_nonneg (fun _ _ => row (params e j)) (fun _ _ => row_nonneg _ hpR hpR1) N
  have envSum := pathLaw_normalized (fun _ _ => row (params e j)) (fun _ _ => row_normalized _) N
  change _ ≤ ∑ h, pathLaw (kernel p q e j) N h*cumulative (fun _ _ x => regretStep j x) N h at hj
  rw [fixed_table_factorization] at hj
  have hnonempty : Nonempty (Hist (I → Bool) N) := ⟨constantHistory (fun _ : I => false) N⟩
  letI := hnonempty
  obtain ⟨table,ht⟩ := ObliviousFactorization.fixed_instance_from_average _ (fixedRegret p q j N)
    envNonneg envSum _ hj
  exact ⟨j,table,ht⟩

end DRGPR.ObliviousInformation
#print axioms DRGPR.ObliviousInformation.step_normalized
#print axioms DRGPR.ObliviousInformation.step_nonneg
#print axioms DRGPR.ObliviousInformation.observable_step
#print axioms DRGPR.ObliviousInformation.conditional_regret
#print axioms DRGPR.ObliviousInformation.visible_law
#print axioms DRGPR.ObliviousInformation.expected_regret
#print axioms DRGPR.ObliviousInformation.fixed_player_normalized
#print axioms DRGPR.ObliviousInformation.fixed_table_factorization
#print axioms DRGPR.ObliviousInformation.exists_fixed_hard_table
