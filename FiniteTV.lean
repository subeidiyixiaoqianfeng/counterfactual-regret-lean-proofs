import FiniteController

noncomputable section
open scoped BigOperators
namespace DRGPR.FiniteTV
open FiniteController
variable {I J : Type} [Fintype I] [Fintype J]

def tv (p q : FiniteController.Dist I) : ℝ := (∑ i, |p.val i-q.val i|)/2

theorem nonneg (p q : FiniteController.Dist I) : 0 ≤ tv p q := by
  unfold tv
  positivity

theorem self (p : FiniteController.Dist I) : tv p p=0 := by simp [tv]

theorem triangle (p q r : FiniteController.Dist I) : tv p r ≤ tv p q+tv q r := by
  have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset I)) =>
    abs_sub_le (p.val i) (q.val i) (r.val i))
  rw [Finset.sum_add_distrib] at h
  dsimp [tv]
  linarith

theorem test_bound (p q : FiniteController.Dist I) (g : I → ℝ)
    (h0 : ∀ i, 0 ≤ g i) (h1 : ∀ i, g i ≤ 1) :
    |DRGPR.mean p.val g-DRGPR.mean q.val g| ≤ tv p q := by
  have hsum : (∑ i, (p.val i-q.val i))=0 := by rw [Finset.sum_sub_distrib,p.sum_one,q.sum_one]; ring
  have he : 2*(DRGPR.mean p.val g-DRGPR.mean q.val g)=
      ∑ i, (p.val i-q.val i)*(2*g i-1) := by
    have ht (i : I) : (p.val i-q.val i)*(2*g i-1)=
        2*(p.val i*g i-q.val i*g i)-(p.val i-q.val i) := by ring
    simp_rw [ht]
    rw [Finset.sum_sub_distrib,← Finset.mul_sum,hsum,Finset.sum_sub_distrib]
    simp only [DRGPR.mean,sub_zero]
  have ha : |∑ i, (p.val i-q.val i)*(2*g i-1)| ≤ ∑ i, |p.val i-q.val i| := by
    calc
      _ ≤ ∑ i, |(p.val i-q.val i)*(2*g i-1)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul]
        have hg : |2*g i-1| ≤ 1 := abs_le.mpr ⟨by linarith [h0 i],by linarith [h1 i]⟩
        simpa using mul_le_mul_of_nonneg_left hg (abs_nonneg (p.val i-q.val i))
  rw [← he,abs_mul] at ha
  norm_num at ha
  dsimp [tv]
  linarith

def push (p : FiniteController.Dist I) (K : I → FiniteController.Dist J) : FiniteController.Dist J where
  val j := ∑ i, p.val i*(K i).val j
  nonneg j := Finset.sum_nonneg (fun i _ => mul_nonneg (p.nonneg i) ((K i).nonneg j))
  sum_one := by rw [Finset.sum_comm]; simp only [← Finset.mul_sum,Dist.sum_one,mul_one]

theorem mixture_bound (p : FiniteController.Dist I) (K L : I → FiniteController.Dist J) :
    tv (push p K) (push p L) ≤ ∑ i, p.val i*tv (K i) (L i) := by
  have hlocal (j : J) : |(push p K).val j-(push p L).val j| ≤
      ∑ i, p.val i*|(K i).val j-(L i).val j| := by
    change |(∑ i, p.val i*(K i).val j)-(∑ i, p.val i*(L i).val j)| ≤ _
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ i, |p.val i*(K i).val j-p.val i*(L i).val j| := Finset.abs_sum_le_sum_abs _ _
      _ = _ := by simp_rw [← mul_sub,abs_mul,abs_of_nonneg (p.nonneg _)]
  have hh := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset J)) => hlocal j)
  rw [Finset.sum_comm] at hh
  simp_rw [← Finset.mul_sum] at hh
  have hr : (∑ i, p.val i*tv (K i) (L i)) =
      (∑ i, (p.val i*(∑ j, |(K i).val j-(L i).val j|)))/2 := by
    unfold tv
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hr]
  exact div_le_div_of_nonneg_right hh (by norm_num)

theorem kernel_perturbation (p : FiniteController.Dist I) (K L : I → FiniteController.Dist J)
    (ε : ℝ) (h : ∀ i, tv (K i) (L i) ≤ ε) : tv (push p K) (push p L) ≤ ε := by
  calc
    _ ≤ ∑ i, p.val i*tv (K i) (L i) := mixture_bound p K L
    _ ≤ ∑ i, p.val i*ε := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (h i) (p.nonneg i))
    _ = ε := by rw [← Finset.sum_mul,p.sum_one,one_mul]

theorem event_bound (p q : FiniteController.Dist I) (s : Finset I) :
    |(∑ i ∈ s, p.val i)-(∑ i ∈ s, q.val i)| ≤ tv p q := by
  classical
  have h := test_bound p q (fun i => if i ∈ s then 1 else 0)
    (fun i => by dsimp only; split_ifs <;> norm_num) (fun i => by dsimp only; split_ifs <;> norm_num)
  simpa [DRGPR.mean,mul_ite] using h

/-- The half-L1 convention equals an attained event difference, not twice it. -/
theorem attaining_event (p q : FiniteController.Dist I) :
    ∃ s : Finset I, tv p q=|(∑ i ∈ s, p.val i)-(∑ i ∈ s, q.val i)| := by
  classical
  let s := Finset.univ.filter (fun i => q.val i ≤ p.val i)
  have ht (i : I) : 2*(if q.val i ≤ p.val i then p.val i-q.val i else 0)=
      |p.val i-q.val i|+(p.val i-q.val i) := by
    by_cases h : q.val i ≤ p.val i
    · rw [if_pos h,abs_of_nonneg (sub_nonneg.mpr h)]; ring
    · rw [if_neg h,abs_of_neg (sub_neg.mpr (lt_of_not_ge h))]; ring
  have hs : (∑ i ∈ s, (p.val i-q.val i))=∑ i, if q.val i ≤ p.val i then p.val i-q.val i else 0 := by
    simp only [s,Finset.sum_filter]
  have he : 2*(∑ i ∈ s, (p.val i-q.val i))=∑ i, |p.val i-q.val i| := by
    rw [hs,Finset.mul_sum]
    simp_rw [ht]
    rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,p.sum_one,q.sum_one]
    ring
  have hp : 0 ≤ ∑ i ∈ s, (p.val i-q.val i) := by
    apply Finset.sum_nonneg
    intro i hi
    exact sub_nonneg.mpr (Finset.mem_filter.mp hi).2
  refine ⟨s,?_⟩
  rw [← Finset.sum_sub_distrib,abs_of_nonneg hp]
  dsimp [tv]
  linarith

end DRGPR.FiniteTV
#print axioms DRGPR.FiniteTV.nonneg
#print axioms DRGPR.FiniteTV.self
#print axioms DRGPR.FiniteTV.triangle
#print axioms DRGPR.FiniteTV.test_bound
#print axioms DRGPR.FiniteTV.mixture_bound
#print axioms DRGPR.FiniteTV.kernel_perturbation
#print axioms DRGPR.FiniteTV.event_bound
#print axioms DRGPR.FiniteTV.attaining_event
