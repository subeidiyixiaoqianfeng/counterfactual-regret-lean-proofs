import PrimitiveJointBounds
import PrimitiveTaskCap
import NativeNoRegret

/-! A local parameter restriction closes a near-matching benchmark without
importing a multiscale switching lower bound. The original binary, primitive
Master model and its paid growing schedule are unchanged. -/
noncomputable section
open scoped BigOperators
namespace DRGPR.SparseFeedbackBenchmark
open Filter
open scoped Topology

theorem cube_le_information (a t q : ℝ) (ha : 0 < a) (ht : 0 < t)
    (hq : 0 < q) (hbalance : q^3*t ≤ a) :
    a^((1:ℝ)/3)*t^((2:ℝ)/3) ≤ Real.sqrt (a*t/q) := by
  let x := a^((1:ℝ)/3)*t^((2:ℝ)/3)
  let y := Real.sqrt (a*t/q)
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hy0 : 0 ≤ y := Real.sqrt_nonneg _
  have hx3 : x^3 = a*t^2 := by
    dsimp [x]
    rw [mul_pow]
    rw [← Real.rpow_natCast (a^((1:ℝ)/3)) 3,
      ← Real.rpow_natCast (t^((2:ℝ)/3)) 3,
      ← Real.rpow_mul ha.le, ← Real.rpow_mul ht.le]
    norm_num
  have hy2 : y^2 = a*t/q := Real.sq_sqrt (by positivity)
  have hq3 : 0 < q^3 := pow_pos hq _
  have hprod := mul_le_mul_of_nonneg_left hbalance (show 0 ≤ a^2*t^3 by positivity)
  have h6 : x^6 ≤ y^6 := by
    have hx6 : x^6 = (a*t^2)^2 := by rw [show x^6 = (x^3)^2 by ring, hx3]
    have hy6 : y^6 = (a*t/q)^3 := by rw [show y^6 = (y^2)^3 by ring, hy2]
    rw [hx6,hy6,div_pow]
    apply (le_div_iff₀ hq3).mpr
    nlinarith only [hprod]
  exact (pow_le_pow_iff_left₀ hx0 hy0 (by norm_num : (6:ℕ) ≠ 0)).mp h6

/-- Finite-time minimax interval in exactly the already-constructed paid model.
The local balance condition is on public parameters, not on an unknown regret. -/
theorem paid_sparse_bounds (B m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hB : 4*m ≤ B)
    (q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1)
    (hbalance : q^3*((m:ℝ)*n) ≤ (m:ℝ)*B*Real.log B) :
    let hK := fun r => PaidSchedule.registered_two B m (r+1) hm hB
    ((1/128:ℝ)*min ((m:ℝ)*n) (Real.sqrt ((m:ℝ)*B*((m:ℝ)*n)/q))-(m:ℝ)/2 ≤
      GrowingTaskLower.minimax hK q n m) ∧
    (GrowingTaskLower.minimax hK q n m ≤
      8*Real.sqrt ((m:ℝ)*B*Real.log B*((m:ℝ)*n)/q)+5*m) := by
  dsimp only
  have h := PrimitiveJointBounds.paid_common_model B m n hm hn hB q hq hq1
  have hmR : (0:ℝ) < m := Nat.cast_pos.mpr hm
  have hnR : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have hBR : (1:ℝ) < B := by exact_mod_cast (show 1 < B by omega)
  have ha : 0 < (m:ℝ)*B*Real.log B :=
    mul_pos (mul_pos hmR (by linarith)) (Real.log_pos hBR)
  have hc := cube_le_information ((m:ℝ)*B*Real.log B) ((m:ℝ)*n) q ha
    (mul_pos hmR hnR) hq hbalance
  exact ⟨h.2.2.2.1, by linarith [h.2.2.2.2]⟩

theorem paid_sparse_capped (B m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hB : 4*m ≤ B)
    (q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1)
    (hbalance : q^3*((m:ℝ)*n) ≤ (m:ℝ)*B*Real.log B) :
    let hK := fun r => PaidSchedule.registered_two B m (r+1) hm hB
    ((1/128:ℝ)*min ((m:ℝ)*n) (Real.sqrt ((m:ℝ)*B*((m:ℝ)*n)/q))-(m:ℝ)/2 ≤
      GrowingTaskLower.minimax hK q n m) ∧
    (GrowingTaskLower.minimax hK q n m ≤ min ((m:ℝ)*n)
      (8*Real.sqrt ((m:ℝ)*B*Real.log B*((m:ℝ)*n)/q)+5*m)) := by
  have h := paid_sparse_bounds B m n hm hn hB q hq hq1 hbalance
  exact ⟨h.1,le_min (PrimitiveTaskCap.minimax_le_horizon _ hn q hq hq1 m) h.2⟩

theorem normalized_information (a T q : ℝ) (ha : 0 ≤ a) (hT : 0 < T) (hq : 0 < q) :
    Real.sqrt (a*T/q)/T = Real.sqrt (a/(q*T)) := by
  have hs := GrowingRate.sqrt_scaling T 1 (a/(q*T)) 1 hT.le (by norm_num)
    (by positivity) (by norm_num)
  have hi : T*(a/(q*T))*(T*1)/1 = a*T/q := by field_simp; ring
  rw [hi] at hs
  simp only [mul_one,div_one] at hs
  rw [← hs]
  exact mul_div_cancel_left₀ _ hT.ne'

/-- A numerical no-regret endpoint for the new information-dominated bound.
Both conditions concern public complexity/resources, not unknown regret. -/
theorem sparse_no_regret (R a T q m : ℕ → ℝ)
    (ha : ∀ k, 0 ≤ a k) (hT : ∀ k, 0 < T k) (hq : ∀ k, 0 < q k)
    (hu : ∀ k, R k ≤ 8*Real.sqrt (a k*T k/q k)+5*m k)
    (hi : Tendsto (fun k => a k/(q k*T k)) atTop (𝓝 0))
    (hm : Tendsto (fun k => m k/T k) atTop (𝓝 0)) :
    Tendsto (fun k => max 0 (R k/T k)) atTop (𝓝 0) := by
  apply NativeNoRegret.upper_no_regret R _ T hT hu
  have he : ∀ k, (8*Real.sqrt (a k*T k/q k)+5*m k)/T k =
      8*Real.sqrt (a k/(q k*T k))+5*(m k/T k) := by
    intro k
    calc
      _ = 8*(Real.sqrt (a k*T k/q k)/T k)+5*(m k/T k) := by ring
      _ = _ := by rw [normalized_information _ _ _ (ha k) (hT k) (hq k)]
  simp_rw [he]
  have hl := (hi.sqrt.const_mul 8).add (hm.const_mul 5)
  simpa using hl

end DRGPR.SparseFeedbackBenchmark
#print axioms DRGPR.SparseFeedbackBenchmark.cube_le_information
#print axioms DRGPR.SparseFeedbackBenchmark.paid_sparse_bounds
#print axioms DRGPR.SparseFeedbackBenchmark.paid_sparse_capped
#print axioms DRGPR.SparseFeedbackBenchmark.normalized_information
#print axioms DRGPR.SparseFeedbackBenchmark.sparse_no_regret
