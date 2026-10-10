import FiniteSimulation
import FiniteBanditLower

noncomputable section
open scoped BigOperators
namespace DRGPR.ErasedProcess
open SupportedInformation FiniteSimulation ErasedBandit
variable {I : Type} [Fintype I] [DecidableEq I]

def observe (x : I × Bool × Bool) : I × Option Bool :=
  (x.1,if x.2.2 then none else some x.2.1)

def raw (p : I → ℝ) (q e : ℝ) (j : I) (x : I × Bool × Bool) : ℝ :=
  p x.1*bernoulli (if x.1=j then 1/2-e else 1/2) x.2.1*bernoulli q x.2.2

def task (x : I × Bool × Bool) : ℝ := if x.2.1 then 0 else 1

theorem raw_normalized (p : I → ℝ) (q e : ℝ) (j : I) (hp : ∑ i, p i=1) :
    ∑ x, raw p q e j x=1 := by
  rw [Fintype.sum_prod_type]
  calc
    _ = ∑ i, p i := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i=j <;>
        simp [raw,bernoulli,Fintype.sum_prod_type,Fintype.sum_bool,hi] <;> ring
    _ = 1 := hp

theorem raw_nonneg (p : I → ℝ) (q e : ℝ) (j : I) (hp : ∀ i, 0 ≤ p i)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (he : 0 ≤ e) (he1 : e ≤ 1/4) (x : I × Bool × Bool) :
    0 ≤ raw p q e j x := by
  apply mul_nonneg
  · apply mul_nonneg (hp x.1)
    cases x.2.1 <;> simp only [bernoulli] <;> split_ifs <;> linarith
  · cases x.2.2 <;> simp only [bernoulli] <;> linarith

theorem observation_kernel (p : I → ℝ) (q e : ℝ) (j : I) (a : I × Option Bool) :
    (∑ x, if observe x=a then raw p q e j x else 0)=joint p q e j a := by
  obtain ⟨i,o⟩ := a
  cases o with
  | none =>
    by_cases hi : i=j <;>
      simp [observe,raw,joint,FiniteInformation.erased,Fintype.sum_prod_type,Fintype.sum_bool,bernoulli,hi] <;> ring
  | some b =>
    cases b <;>
      simp [observe,raw,joint,FiniteInformation.erased,Fintype.sum_prod_type,Fintype.sum_bool,bernoulli] <;> ring

def fullKernel
    (p : (n : ℕ) → Hist (I × Option Bool) n → I → ℝ) (q e : ℝ) (j : I)
    (n : ℕ) (h : Hist (I × Bool × Bool) n) : I × Bool × Bool → ℝ :=
  raw (p n (project observe n h)) q e j

theorem actual_observation_law
    (p : (n : ℕ) → Hist (I × Option Bool) n → I → ℝ) (q e : ℝ) (j : I)
    (n : ℕ) (h : Hist (I × Option Bool) n) :
    (∑ g, if project observe n g=h then pathLaw (fullKernel p q e j) n g else 0)=
      pathLaw (fun t past => joint (p t past) q e j) n h := by
  exact projected_path_law observe _ _
    (fun t g a => observation_kernel (p t (project observe t g)) q e j a) n h

theorem task_is_bounded (x : I × Bool × Bool) : 0 ≤ task x ∧ task x ≤ 1 := by
  unfold task
  split_ifs <;> constructor <;> norm_num

theorem one_round_loss (p : I → ℝ) (q e : ℝ) (j : I) :
    (∑ x, raw p q e j x*(task x-(1/2-e))) =
      ∑ x, raw p q e j x*(e*(1-(if x.1=j then 1 else 0))) := by
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i=j <;>
    simp [raw,task,hi,bernoulli,Fintype.sum_bool] <;> ring

theorem mean_gap_counts (p : (n : ℕ) → Hist (I × Option Bool) n → I → ℝ)
    (hp : ∀ n h, ∑ i, p n h i=1) (q e : ℝ) (j : I) (N : ℕ) :
    (∑ h, pathLaw (fullKernel p q e j) N h*
      cumulative (fun _ _ x => task x-(1/2-e)) N h) =
    e*((N:ℝ)-(∑ h, pathLaw (fun t h => joint (p t h) q e j) N h*counts j N h)) := by
  let k := fun t h => joint (p t h) q e j
  let l := fullKernel p q e j
  let c := fun (_t : ℕ) (_h : Hist (I × Option Bool) _t) (x : I × Option Bool) =>
    e*(1-(if x.1=j then 1 else 0))
  have hls : ∀ t h, ∑ x, l t h x=1 :=
    fun t h => raw_normalized _ q e j (hp t (project observe t h))
  have hequal : (∑ h, pathLaw l N h*cumulative (fun _ _ x => task x-(1/2-e)) N h)=
      ∑ h, pathLaw l N h*cumulative (fun t h x => c t (project observe t h) (observe x)) N h := by
    rw [expected_cumulative _ _ hls,expected_cumulative _ _ hls]
    apply Finset.sum_congr rfl
    intro t _
    apply Finset.sum_congr rfl
    intro h _
    congr 1
    exact one_round_loss (p t (project observe t h)) q e j
  rw [hequal]
  simp_rw [cumulative_projection]
  rw [projected_expectation observe k l
    (fun t h a => observation_kernel (p t (project observe t h)) q e j a)]
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

end DRGPR.ErasedProcess
#print axioms DRGPR.ErasedProcess.raw_normalized
#print axioms DRGPR.ErasedProcess.raw_nonneg
#print axioms DRGPR.ErasedProcess.observation_kernel
#print axioms DRGPR.ErasedProcess.actual_observation_law
#print axioms DRGPR.ErasedProcess.task_is_bounded
#print axioms DRGPR.ErasedProcess.one_round_loss
#print axioms DRGPR.ErasedProcess.mean_gap_counts
