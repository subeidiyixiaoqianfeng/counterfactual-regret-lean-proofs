import RestartedGrowing

noncomputable section
open scoped BigOperators
namespace DRGPR.GrowingRate
open RestartedGrowing

theorem entropy_mono (K B : ℝ) (hK : 1 ≤ K) (hKB : K ≤ B) :
    K*Real.log K ≤ B*Real.log B := by
  have hk : 0 < K := by linarith
  exact mul_le_mul hKB (Real.log_le_log hk hKB) (Real.log_nonneg hK) (by linarith)

theorem phase_bound_uniform (M : Model) (B : ℝ) (r : ℕ) (hB : (M.K r:ℝ) ≤ B) :
    M.upper r ≤ 4*((B*Real.log B)^((1:ℝ)/3)*(M.n:ℝ)^((2:ℝ)/3)+
      Real.sqrt (B*Real.log B*M.n/M.q)+1) := by
  have hk : (1:ℝ) ≤ M.K r := by have := M.K_two r; exact_mod_cast (by omega : 1 ≤ M.K r)
  have ha := entropy_mono (M.K r) B hk hB
  have ha0 : 0 ≤ (M.K r:ℝ)*Real.log (M.K r) := mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg hk)
  have hr := Real.rpow_le_rpow ha0 ha (by norm_num : (0:ℝ) ≤ 1/3)
  have hp := mul_le_mul_of_nonneg_right hr (Real.rpow_nonneg (Nat.cast_nonneg M.n) ((2:ℝ)/3))
  have hq := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right ha (Nat.cast_nonneg M.n)) M.q_pos.le
  have hs := Real.sqrt_le_sqrt hq
  unfold Model.upper
  linarith

theorem cube_scaling (m n a : ℝ) (hm : 0 < m) (hn : 0 ≤ n) (ha : 0 ≤ a) :
    m*(a^((1:ℝ)/3)*n^((2:ℝ)/3))=(m*a)^((1:ℝ)/3)*(m*n)^((2:ℝ)/3) := by
  have he : m^((1:ℝ)/3)*m^((2:ℝ)/3)=m := by rw [← Real.rpow_add hm]; norm_num
  rw [Real.mul_rpow hm.le ha,Real.mul_rpow hm.le hn]
  calc
    _ = (m^((1:ℝ)/3)*m^((2:ℝ)/3))*(a^((1:ℝ)/3)*n^((2:ℝ)/3)) := by rw [he]
    _ = _ := by ring

theorem sqrt_scaling (m n a q : ℝ) (hm : 0 ≤ m) (hn : 0 ≤ n) (ha : 0 ≤ a) (hq : 0 < q) :
    m*Real.sqrt (a*n/q)=Real.sqrt (m*a*(m*n)/q) := by
  have hv : 0 ≤ a*n/q := by positivity
  have hl := Real.sq_sqrt hv
  have hr := Real.sq_sqrt (show 0 ≤ m*a*(m*n)/q by positivity)
  have hsq : (m*Real.sqrt (a*n/q))^2=m*a*(m*n)/q := by
    calc
      _ = m^2*(Real.sqrt (a*n/q))^2 := by ring
      _ = _ := by rw [hl]; ring
  have h0 : 0 ≤ m*Real.sqrt (a*n/q) := mul_nonneg hm (Real.sqrt_nonneg _)
  have h1 := Real.sqrt_nonneg (m*a*(m*n)/q)
  nlinarith

theorem joint_upper (M : Model) (m : ℕ) (hm : 0 < m) (B : ℝ)
    (hB : ∀ r < m, (M.K r:ℝ) ≤ B) :
    M.learnerCost m-sInf (Set.range (fun v : (r : ℕ) → Fin (M.K r) => M.comparatorCost v m)) ≤
      4*((m*B*Real.log B)^((1:ℝ)/3)*((m:ℝ)*M.n)^((2:ℝ)/3)+
        Real.sqrt (m*B*Real.log B*((m:ℝ)*M.n)/M.q))+5*m := by
  have hK0 : (1:ℝ) ≤ M.K 0 := by have := M.K_two 0; exact_mod_cast (by omega : 1 ≤ M.K 0)
  have hB1 : 1 ≤ B := hK0.trans (hB 0 hm)
  have ha0 : 0 ≤ B*Real.log B := mul_nonneg (by linarith) (Real.log_nonneg hB1)
  have hmR : (0:ℝ) < m := Nat.cast_pos.mpr hm
  have hs := Finset.sum_le_sum (fun r (hr : r ∈ Finset.range m) =>
    add_le_add_right (phase_bound_uniform M B r (hB r (Finset.mem_range.mp hr))) (1/2:ℝ))
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul] at hs
  have h := le_trans (M.counterfactual_infimum m) hs
  have hc := cube_scaling (m:ℝ) (M.n:ℝ) (B*Real.log B) hmR (Nat.cast_nonneg _) ha0
  have hsq := sqrt_scaling (m:ℝ) (M.n:ℝ) (B*Real.log B) M.q hmR.le
    (Nat.cast_nonneg _) ha0 M.q_pos
  have hform : (m:ℝ)*(4*((B*Real.log B)^((1:ℝ)/3)*(M.n:ℝ)^((2:ℝ)/3)+
      Real.sqrt (B*Real.log B*M.n/M.q)+1)+1/2)=
    4*(((m:ℝ)*B*Real.log B)^((1:ℝ)/3)*((m:ℝ)*M.n)^((2:ℝ)/3)+
      Real.sqrt ((m:ℝ)*B*Real.log B*((m:ℝ)*M.n)/M.q))+(9/2:ℝ)*m := by
    have hc' := hc
    have hs' := hsq
    simp only [← mul_assoc] at hc' hs' ⊢
    nlinarith
  rw [hform] at h
  nlinarith

end DRGPR.GrowingRate
#print axioms DRGPR.GrowingRate.entropy_mono
#print axioms DRGPR.GrowingRate.phase_bound_uniform
#print axioms DRGPR.GrowingRate.cube_scaling
#print axioms DRGPR.GrowingRate.sqrt_scaling
#print axioms DRGPR.GrowingRate.joint_upper
