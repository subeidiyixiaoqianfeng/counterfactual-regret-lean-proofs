import FiniteInformation
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! A finite relative-entropy testing inequality proved through Hellinger
distance. Its constant is weaker than sharp Pinsker but sufficient for the
stated order of the information lower bound. Both distributions are positive
on their common support. Zero-probability impossible histories must first be
removed or separately justified by an absolute-continuity argument. -/
noncomputable section
open scoped BigOperators
namespace DRGPR.FiniteTesting
open DRGPR.FiniteInformation

theorem root_log_bound (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    2*(p-Real.sqrt p*Real.sqrt q) ≤ p*Real.log (p/q) := by
  have hs := Real.log_le_sub_one_of_pos (div_pos (Real.sqrt_pos.2 hq) (Real.sqrt_pos.2 hp))
  rw [Real.log_div (Real.sqrt_pos.2 hq).ne' (Real.sqrt_pos.2 hp).ne',
    Real.log_sqrt hq.le, Real.log_sqrt hp.le] at hs
  have he : p*(Real.sqrt q/Real.sqrt p)=Real.sqrt p*Real.sqrt q := by
    calc
      _ = (Real.sqrt p)^2*(Real.sqrt q/Real.sqrt p) := by rw [Real.sq_sqrt hp.le]
      _ = _ := by
        field_simp [(Real.sqrt_pos.2 hp).ne']
        nlinarith [congrArg (fun x : ℝ => x*Real.sqrt q) (Real.sq_sqrt hp.le)]
  have h := mul_le_mul_of_nonneg_left hs hp.le
  simp only [mul_sub, he, mul_one] at h
  rw [Real.log_div hp.ne' hq.ne']
  nlinarith

def hellinger {I : Type*} [Fintype I] (p q : I → ℝ) : ℝ :=
  ∑ i, (Real.sqrt (p i)-Real.sqrt (q i))^2

theorem hellinger_le_kl {I : Type*} [Fintype I] (p q : I → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hac : ∀ i, 0 < p i → 0 < q i)
    (hp1 : ∑ i, p i=1) (hq1 : ∑ i, q i=1) :
    hellinger p q ≤ divergence p q := by
  have hlocal (i : I) : 2*(p i-Real.sqrt (p i)*Real.sqrt (q i)) ≤ p i*Real.log (p i/q i) := by
    by_cases h : p i=0
    · simp [h]
    · have hpos : 0 < p i := lt_of_le_of_ne (hp i) (Ne.symm h)
      exact root_log_bound (p i) (q i) hpos (hac i hpos)
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hlocal i)
  have he : hellinger p q = ∑ i, 2*(p i-Real.sqrt (p i)*Real.sqrt (q i)) := by
    unfold hellinger
    have hf (i : I) : (Real.sqrt (p i)-Real.sqrt (q i))^2 =
        p i+q i-2*(Real.sqrt (p i)*Real.sqrt (q i)) := by
      have h₁ := Real.sq_sqrt (hp i)
      have h₂ := Real.sq_sqrt (hq i)
      nlinarith
    simp_rw [hf, mul_sub]
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hp1, hq1]
    ring
  rw [he]
  exact hh

theorem l1_square_le_hellinger {I : Type*} [Fintype I] (p q : I → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hp1 : ∑ i, p i=1) (hq1 : ∑ i, q i=1) :
    (∑ i, |p i-q i|)^2 ≤ 4*hellinger p q := by
  have he (i : I) : |p i-q i| =
      |Real.sqrt (p i)-Real.sqrt (q i)| * (Real.sqrt (p i)+Real.sqrt (q i)) := by
    have h : p i-q i=(Real.sqrt (p i)-Real.sqrt (q i))*(Real.sqrt (p i)+Real.sqrt (q i)) := by
      have h₁ := Real.sq_sqrt (hp i)
      have h₂ := Real.sq_sqrt (hq i)
      nlinarith
    rw [h, abs_mul, abs_of_nonneg (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i => |Real.sqrt (p i)-Real.sqrt (q i)|)
    (fun i => Real.sqrt (p i)+Real.sqrt (q i))
  have hb : (∑ i, (Real.sqrt (p i)+Real.sqrt (q i))^2) ≤ 4 := by
    calc
      _ ≤ ∑ i, 2*(p i+q i) := by
        apply Finset.sum_le_sum
        intro i _
        have h₁ := Real.sq_sqrt (hp i)
        have h₂ := Real.sq_sqrt (hq i)
        nlinarith [sq_nonneg (Real.sqrt (p i)-Real.sqrt (q i))]
      _ = 4 := by rw [← Finset.mul_sum, Finset.sum_add_distrib, hp1, hq1]; norm_num
  simp_rw [← he, sq_abs] at hc
  have hn : 0 ≤ hellinger p q := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  exact le_trans hc (by simpa [hellinger, mul_comm] using mul_le_mul_of_nonneg_left hb hn)

theorem bounded_test {I : Type*} [Fintype I] (p q f : I → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hac : ∀ i, 0 < p i → 0 < q i)
    (hp1 : ∑ i, p i=1) (hq1 : ∑ i, q i=1)
    (hf0 : ∀ i, 0 ≤ f i) (hf1 : ∀ i, f i ≤ 1) :
    |(∑ i, q i*f i)-(∑ i, p i*f i)| ≤ Real.sqrt (divergence p q) := by
  have hc : (∑ i, (q i-p i)*(f i-1/2)) = (∑ i, q i*f i)-(∑ i, p i*f i) := by
    simp_rw [sub_mul, mul_sub]
    simp only [Finset.sum_sub_distrib, ← Finset.sum_mul, hp1, hq1]
    ring
  have habs : |(∑ i, q i*f i)-(∑ i, p i*f i)| ≤ (∑ i, |p i-q i|)/2 := by
    rw [← hc]
    calc
      _ ≤ ∑ i, |(q i-p i)*(f i-1/2)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, |p i-q i|/2 := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul, abs_sub_comm (q i) (p i)]
        have hf : |f i-1/2| ≤ (1:ℝ)/2 := abs_le.mpr ⟨by linarith [hf0 i], by linarith [hf1 i]⟩
        simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hf (abs_nonneg (p i-q i))
      _ = _ := by rw [Finset.sum_div]
  have hh := l1_square_le_hellinger p q hp hq hp1 hq1
  have hk := hellinger_le_kl p q hp hq hac hp1 hq1
  have hkn : 0 ≤ divergence p q := le_trans (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) hk
  have hs := Real.sq_sqrt hkn
  have hr := Real.sqrt_nonneg (divergence p q)
  have hn : 0 ≤ ∑ i, |p i-q i| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hb : (∑ i, |p i-q i|)/2 ≤ Real.sqrt (divergence p q) := by nlinarith
  exact le_trans habs hb

end DRGPR.FiniteTesting
#print axioms DRGPR.FiniteTesting.root_log_bound
#print axioms DRGPR.FiniteTesting.hellinger_le_kl
#print axioms DRGPR.FiniteTesting.l1_square_le_hellinger
#print axioms DRGPR.FiniteTesting.bounded_test
