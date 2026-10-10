import GrowingTaskLower
import PaidSchedule
import GrowingRate

noncomputable section
open scoped BigOperators
namespace DRGPR.PaidInformationLower
open PaidSchedule

theorem half_registered (B m r : ℕ) : (B:ℝ)/2 ≤ registered B m r := by
  have hc : B ≤ 2*core B := by unfold core; omega
  have hr : core B ≤ registered B m r := Nat.le_add_right _ _
  have hcR : (B:ℝ) ≤ 2*(core B:ℝ) := by exact_mod_cast hc
  have hrR : (core B:ℝ) ≤ registered B m r := by exact_mod_cast hr
  linarith

theorem phase_lower_uniform (B m n r : ℕ) (q : ℝ) (hq : 0 < q) :
    (1/64:ℝ)*min (n:ℝ) (Real.sqrt ((B:ℝ)*n/q)) ≤
      GrowingInformation.lower (fun s => registered B m (s+1)) n q r := by
  have hK := half_registered B m (r+1)
  have hn : (0:ℝ) ≤ n := Nat.cast_nonneg _
  have hx := Real.sq_sqrt (show 0 ≤ (B:ℝ)*n/q by positivity)
  have hy := Real.sq_sqrt (show 0 ≤ (registered B m (r+1):ℝ)*n/q by positivity)
  have hx0 := Real.sqrt_nonneg ((B:ℝ)*n/q)
  have hy0 := Real.sqrt_nonneg ((registered B m (r+1):ℝ)*n/q)
  have hm := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hK hn) hq.le
  have hs : Real.sqrt ((B:ℝ)*n/q)/2 ≤ Real.sqrt ((registered B m (r+1):ℝ)*n/q) := by
    have he : ((B:ℝ)/2*n)/q=((B:ℝ)*n/q)/2 := by ring
    rw [he] at hm
    nlinarith
  have hl : min (n:ℝ) (Real.sqrt ((B:ℝ)*n/q))/2 ≤
      min (n:ℝ) (Real.sqrt ((registered B m (r+1):ℝ)*n/q)) := by
    apply le_min
    · have := min_le_left (n:ℝ) (Real.sqrt ((B:ℝ)*n/q)); linarith
    · have := min_le_right (n:ℝ) (Real.sqrt ((B:ℝ)*n/q)); linarith
  unfold GrowingInformation.lower
  linarith

/-- Information lower bound in the paid nested-library model, including
actual learner switches and the comparator boundary correction.
This does not prove the multiscale switching-cost rate. -/
theorem paid_minimax_lower (B m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hB : 4*m ≤ B)
    (q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1) :
    (1/128:ℝ)*min ((m:ℝ)*n) (Real.sqrt ((m:ℝ)*B*((m:ℝ)*n)/q))-(m:ℝ)/2 ≤
      GrowingTaskLower.minimax (fun r => registered_two B m (r+1) hm hB) q n m := by
  have h := GrowingTaskLower.minimax_lower q n m hn
    (fun r => registered_two B m (r+1) hm hB) hq hq1
  have hs := Finset.sum_le_sum (fun r (_ : r ∈ Finset.range m) => phase_lower_uniform B m n r q hq)
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul] at hs
  have hscale := GrowingRate.sqrt_scaling (m:ℝ) (n:ℝ) (B:ℝ) q
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) hq
  have hmin : (m:ℝ)*min (n:ℝ) (Real.sqrt ((B:ℝ)*n/q))=
      min ((m:ℝ)*n) (Real.sqrt ((m:ℝ)*B*((m:ℝ)*n)/q)) := by
    rw [mul_min_of_nonneg _ _ (Nat.cast_nonneg m),hscale]
  have he : (m:ℝ)*((1/64:ℝ)*min (n:ℝ) (Real.sqrt ((B:ℝ)*n/q)))=
      (1/64:ℝ)*min ((m:ℝ)*n) (Real.sqrt ((m:ℝ)*B*((m:ℝ)*n)/q)) := by
    calc
      _ = (1/64:ℝ)*((m:ℝ)*min (n:ℝ) (Real.sqrt ((B:ℝ)*n/q))) := by ring
      _ = _ := by rw [hmin]
  rw [he] at hs
  linarith

end DRGPR.PaidInformationLower
#print axioms DRGPR.PaidInformationLower.half_registered
#print axioms DRGPR.PaidInformationLower.phase_lower_uniform
#print axioms DRGPR.PaidInformationLower.paid_minimax_lower
