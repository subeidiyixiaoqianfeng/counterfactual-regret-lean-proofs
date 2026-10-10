import SupportedInformation

noncomputable section
open scoped BigOperators
namespace DRGPR.ErasedBandit
open DRGPR.FiniteInformation DRGPR.SupportedInformation

def bernoulli (a : ℝ) : Bool → ℝ | false => a | true => 1-a

theorem bernoulli_normalized (a : ℝ) : (∑ b, bernoulli a b)=1 := by
  simp [bernoulli, Fintype.sum_bool]

theorem bernoulli_positive (a : ℝ) (ha : 0 < a) (ha1 : a < 1) :
    ∀ b, 0 < bernoulli a b := by intro b; cases b <;> simp [bernoulli] <;> linarith

theorem bernoulli_divergence (e : ℝ) (he : 0 ≤ e) (he1 : e ≤ 1/4) :
    divergence (bernoulli (1/2)) (bernoulli (1/2-e)) = -(1/2:ℝ)*Real.log (1-4*e^2) := by
  have ha : 0 < (1/2:ℝ)-e := by linarith
  have hb : 0 < (1/2:ℝ)+e := by linarith
  have hd : 0 < 1-4*e^2 := by nlinarith
  have hprod : ((1/2:ℝ)/(1/2-e))*((1/2:ℝ)/(1/2+e)) = (1-4*e^2)⁻¹ := by
    rw [← mul_div_mul_comm, inv_eq_one_div]
    apply (div_eq_div_iff (mul_pos ha hb).ne' hd.ne').2
    ring
  have hl := Real.log_mul (div_pos (by norm_num : 0 < (1/2:ℝ)) ha).ne'
    (div_pos (by norm_num : 0 < (1/2:ℝ)) hb).ne'
  rw [hprod, Real.log_inv] at hl
  simp only [divergence, Fintype.sum_bool, bernoulli]
  have hsub : (1:ℝ)-(1/2-e)=1/2+e := by ring
  rw [hsub]
  norm_num only at *
  nlinarith

theorem erased_normalized (q a : ℝ) : (∑ o, erased q (bernoulli a) o)=1 := by
  rw [Fintype.sum_option]
  simp only [erased, ← Finset.mul_sum, bernoulli_normalized]
  ring

theorem erased_nonneg (q a : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (ha : 0 ≤ a) (ha1 : a ≤ 1) : ∀ o, 0 ≤ erased q (bernoulli a) o := by
  intro o
  cases o with
  | none => simp only [erased]; linarith
  | some b =>
    cases b
    · exact mul_nonneg hq ha
    · exact mul_nonneg hq (sub_nonneg.mpr ha1)

theorem erased_support (q a a' : ℝ) (hq : 0 < q)
    (ha : 0 < a') (ha1 : a' < 1) :
    ∀ o, 0 < erased q (bernoulli a) o → 0 < erased q (bernoulli a') o := by
  intro o h
  cases o with
  | none => exact h
  | some b => exact mul_pos hq (bernoulli_positive a' ha ha1 b)

theorem erased_kl_bound (q e : ℝ) (hq : 0 < q) (hq1 : q ≤ 1)
    (he : 0 ≤ e) (he1 : e ≤ 1/4) :
    divergence (erased q (bernoulli (1/2))) (erased q (bernoulli (1/2-e))) ≤ 4*q*e^2 := by
  rw [erasure_factor _ _ q hq hq1, bernoulli_divergence e he he1]
  have h := mul_le_mul_of_nonneg_left (DRGPR.bernoulli_kl_scalar_bound e he he1) hq.le
  nlinarith

def joint {I : Type} [DecidableEq I] (p : I → ℝ) (q e : ℝ) (j : I) :
    I × Option Bool → ℝ := fun x => p x.1*erased q (bernoulli (if x.1=j then 1/2-e else 1/2)) x.2

theorem joint_normalized {I : Type} [Fintype I] [DecidableEq I]
    (p : I → ℝ) (q e : ℝ) (j : I) (hp1 : ∑ i, p i=1) :
    (∑ x, joint p q e j x)=1 := by
  unfold joint
  rw [Fintype.sum_prod_type]
  calc
    _ = ∑ i, p i := by
      apply Finset.sum_congr rfl
      intro i _
      change (∑ o, p i*erased q (bernoulli (if i=j then 1/2-e else 1/2)) o)=p i
      rw [← Finset.mul_sum, erased_normalized]
      ring
    _ = 1 := hp1

theorem joint_nonneg {I : Type} [DecidableEq I]
    (p : I → ℝ) (q e : ℝ) (j : I) (hp : ∀ i, 0 ≤ p i)
    (hq : 0 < q) (hq1 : q ≤ 1) (he : 0 ≤ e) (he1 : e ≤ 1/4) :
    ∀ x, 0 ≤ joint p q e j x := by
  intro x
  apply mul_nonneg (hp x.1)
  apply erased_nonneg q _ hq.le hq1
  all_goals split_ifs <;> linarith

theorem joint_support {I : Type} [DecidableEq I]
    (p : I → ℝ) (q e : ℝ) (j : I) (hp : ∀ i, 0 ≤ p i)
    (hq : 0 < q) (hq1 : q ≤ 1) (he : 0 ≤ e) (he1 : e ≤ 1/4) :
    ∀ x, 0 < joint p q 0 j x → 0 < joint p q e j x := by
  intro x h
  have hn := erased_nonneg q (if x.1=j then 1/2-0 else 1/2) hq.le hq1
    (by split_ifs <;> norm_num) (by split_ifs <;> norm_num) x.2
  have hp' : 0 < p x.1 := pos_of_mul_pos_left h hn
  have ho := pos_of_mul_pos_right h (hp x.1)
  apply mul_pos hp'
  apply erased_support q _ _ hq _ _ x.2 ho
  all_goals split_ifs <;> linarith

theorem joint_kl {I : Type} [Fintype I] [DecidableEq I]
    (p : I → ℝ) (q e : ℝ) (j : I) (hp : ∀ i, 0 ≤ p i)
    (hq : 0 < q) (hq1 : q ≤ 1) (he : 0 ≤ e) (he1 : e ≤ 1/4) :
    divergence (joint p q 0 j) (joint p q e j) ≤ 4*q*e^2*p j := by
  have hbase (i : I) : (if i=j then (1/2:ℝ)-0 else 1/2)=1/2 := by split_ifs <;> ring
  unfold joint
  simp_rw [hbase]
  rw [SupportedInformation.chain_rule p p
    (fun _ => erased q (bernoulli (1/2)))
    (fun i => erased q (bernoulli (if i=j then 1/2-e else 1/2))) hp (fun _ h => h)
    (fun _ o => erased_nonneg q (1/2) hq.le hq1 (by norm_num) (by norm_num) o)
    (fun i o h => erased_support q (1/2) _ hq (by split_ifs <;> linarith)
      (by split_ifs <;> linarith) o h) (fun _ => erased_normalized q (1/2))]
  have hself : divergence p p=0 := by
    apply Finset.sum_eq_zero
    intro i _
    by_cases h : p i=0 <;> simp [h]
  rw [hself, zero_add]
  have hdiag (a : ℝ) : divergence (erased q (bernoulli a)) (erased q (bernoulli a))=0 := by
    apply Finset.sum_eq_zero
    intro o _
    by_cases h : erased q (bernoulli a) o=0 <;> simp [h]
  have hterm (i : I) : p i*divergence (erased q (bernoulli (1/2)))
      (erased q (bernoulli (if i=j then 1/2-e else 1/2))) =
      if i=j then p j*divergence (erased q (bernoulli (1/2)))
        (erased q (bernoulli (1/2-e))) else 0 := by
    by_cases h : i=j
    · simp [h]
    · simp [h, hdiag]
  simp_rw [hterm]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]
  have h := mul_le_mul_of_nonneg_left (erased_kl_bound q e hq hq1 he he1) (hp j)
  nlinarith

def counts {I : Type} [DecidableEq I] (j : I) :
    (n : ℕ) → Hist (I × Option Bool) n → ℝ :=
  cumulative (fun _ _ x => if x.1=j then 1 else 0)

theorem count_bounds {I : Type} [DecidableEq I] (j : I) :
    ∀ n h, 0 ≤ counts j n h ∧ counts j n h ≤ n := by
  intro n
  induction n with
  | zero => intro h; simp [counts, cumulative]
  | succ n ih =>
    intro h
    have hprev := ih h.1
    change 0 ≤ counts j n h.1+(if h.2.1=j then 1 else 0) ∧
      counts j n h.1+(if h.2.1=j then 1 else 0) ≤ (n+1:ℕ)
    push_cast
    split_ifs <;> constructor <;> linarith

theorem conditional_count {I : Type} [Fintype I] [DecidableEq I]
    (p : I → ℝ) (q : ℝ) (j : I) :
    (∑ x, joint p q 0 j x*(if x.1=j then 1 else 0))=p j := by
  rw [Fintype.sum_prod_type]
  have hterm (i : I) : (∑ o, joint p q 0 j (i,o)*(if i=j then 1 else 0)) =
      if i=j then p j else 0 := by
    by_cases h : i=j
    · subst i
      simp only [joint, if_true, mul_one, ← Finset.mul_sum, erased_normalized]
    · simp [h]
  simp_rw [hterm]
  simp

theorem transcript_kl {I : Type} [Fintype I] [DecidableEq I]
    (p : (n : ℕ) → Hist (I × Option Bool) n → I → ℝ)
    (hp : ∀ n h i, 0 ≤ p n h i) (hp1 : ∀ n h, ∑ i, p n h i=1)
    (q e : ℝ) (j : I) (N : ℕ)
    (hq : 0 < q) (hq1 : q ≤ 1) (he : 0 ≤ e) (he1 : e ≤ 1/4) :
    divergence (pathLaw (fun n h => joint (p n h) q 0 j) N)
      (pathLaw (fun n h => joint (p n h) q e j) N) ≤
      4*q*e^2*(∑ h, pathLaw (fun n h => joint (p n h) q 0 j) N h*counts j N h) := by
  let k := fun n h => joint (p n h) q 0 j
  let l := fun n h => joint (p n h) q e j
  have hk := fun n h => joint_nonneg (p n h) q 0 j (hp n h) hq hq1 (le_refl 0) (by norm_num)
  have hl := fun n h => joint_support (p n h) q e j (hp n h) hq hq1 he he1
  have hks := fun n h => joint_normalized (p n h) q 0 j (hp1 n h)
  change divergence (pathLaw k N) (pathLaw l N) ≤ _
  rw [adaptive_chain k l hk hl hks N]
  have hc := expected_cumulative k (fun _ _ x => if x.1=j then 1 else 0) hks N
  change (∑ h, pathLaw k N h*counts j N h)=_ at hc
  simp only [k, conditional_count] at hc
  rw [hc, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro h _
  have ht := mul_le_mul_of_nonneg_left (joint_kl (p n h) q e j (hp n h) hq hq1 he he1)
    (pathLaw_nonneg k hk n h)
  simpa only [k, l, mul_assoc, mul_left_comm] using ht

theorem count_compare {I : Type} [Fintype I] [DecidableEq I]
    (p : (n : ℕ) → Hist (I × Option Bool) n → I → ℝ)
    (hp : ∀ n h i, 0 ≤ p n h i) (hp1 : ∀ n h, ∑ i, p n h i=1)
    (q e : ℝ) (j : I) (N : ℕ) (hN : 0 < N)
    (hq : 0 < q) (hq1 : q ≤ 1) (he : 0 ≤ e) (he1 : e ≤ 1/4) :
    (∑ h, pathLaw (fun n h => joint (p n h) q e j) N h*counts j N h) ≤
      (∑ h, pathLaw (fun n h => joint (p n h) q 0 j) N h*counts j N h) +
      N*Real.sqrt (4*q*e^2*(∑ h, pathLaw (fun n h => joint (p n h) q 0 j) N h*counts j N h)) := by
  let k := fun n h => joint (p n h) q 0 j
  let l := fun n h => joint (p n h) q e j
  have hk := fun n h => joint_nonneg (p n h) q 0 j (hp n h) hq hq1 (le_refl 0) (by norm_num)
  have hl := fun n h => joint_nonneg (p n h) q e j (hp n h) hq hq1 he he1
  have hac := fun n h => joint_support (p n h) q e j (hp n h) hq hq1 he he1
  have hk1 := fun n h => joint_normalized (p n h) q 0 j (hp1 n h)
  have hl1 := fun n h => joint_normalized (p n h) q e j (hp1 n h)
  have hn : (0:ℝ) < N := by exact_mod_cast hN
  have hf0 : ∀ h, 0 ≤ counts j N h/(N:ℝ) := fun h => div_nonneg (count_bounds j N h).1 hn.le
  have hf1 : ∀ h, counts j N h/(N:ℝ) ≤ 1 := by
    intro h
    exact (div_le_one hn).2 (count_bounds j N h).2
  have ht := FiniteTesting.bounded_test (pathLaw k N) (pathLaw l N)
    (fun h => counts j N h/(N:ℝ)) (pathLaw_nonneg k hk N) (pathLaw_nonneg l hl N)
    (pathLaw_support k l hk hac N) (pathLaw_normalized k hk1 N) (pathLaw_normalized l hl1 N) hf0 hf1
  simp only [← mul_div_assoc, ← Finset.sum_div, ← sub_div] at ht
  have hd := le_trans (le_abs_self _) ht
  have hd' := (div_le_iff₀ hn).mp hd
  have hkl := transcript_kl p hp hp1 q e j N hq hq1 he he1
  have hs := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hkl) hn.le
  change (∑ h, pathLaw l N h*counts j N h) ≤
    (∑ h, pathLaw k N h*counts j N h) + _
  change N*Real.sqrt (divergence (pathLaw k N) (pathLaw l N)) ≤ _ at hs
  nlinarith

end DRGPR.ErasedBandit
#print axioms DRGPR.ErasedBandit.bernoulli_normalized
#print axioms DRGPR.ErasedBandit.bernoulli_positive
#print axioms DRGPR.ErasedBandit.bernoulli_divergence
#print axioms DRGPR.ErasedBandit.erased_normalized
#print axioms DRGPR.ErasedBandit.erased_nonneg
#print axioms DRGPR.ErasedBandit.erased_support
#print axioms DRGPR.ErasedBandit.erased_kl_bound
#print axioms DRGPR.ErasedBandit.joint_normalized
#print axioms DRGPR.ErasedBandit.joint_nonneg
#print axioms DRGPR.ErasedBandit.joint_support
#print axioms DRGPR.ErasedBandit.joint_kl
#print axioms DRGPR.ErasedBandit.count_bounds
#print axioms DRGPR.ErasedBandit.conditional_count
#print axioms DRGPR.ErasedBandit.transcript_kl
#print axioms DRGPR.ErasedBandit.count_compare
