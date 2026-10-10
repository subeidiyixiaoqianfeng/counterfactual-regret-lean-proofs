import ErasedBandit

noncomputable section
open scoped BigOperators
namespace DRGPR.InformationRate

theorem average_count {I : Type*} [Fintype I] (x y : I → ℝ) (n q e : ℝ)
    (hK : (2:ℝ) ≤ Fintype.card I) (hn : 0 ≤ n) (hq : 0 ≤ q) (he : 0 ≤ e)
    (hx : ∀ i, 0 ≤ x i) (hxs : ∑ i, x i=n)
    (hy : ∀ i, y i ≤ x i+n*Real.sqrt (4*q*e^2*x i))
    (hgap : 64*q*e^2*n ≤ Fintype.card I) :
    (∑ i, y i)/(Fintype.card I:ℝ) ≤ 3*n/4 := by
  let K : ℝ := Fintype.card I
  have hK0 : 0 < K := by dsimp [K]; linarith
  let z := fun i => Real.sqrt (4*q*e^2*x i)
  have hz : ∀ i, 0 ≤ z i := fun i => Real.sqrt_nonneg _
  have hzsq : (∑ i, z i)^2 ≤ K*(4*q*e^2*n) := by
    have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : I => (1:ℝ)) z
    simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hc
    have hs : (∑ i, (z i)^2)=4*q*e^2*n := by
      have hzsq (i : I) : (z i)^2=4*q*e^2*x i :=
        Real.sq_sqrt (mul_nonneg (by positivity) (hx i))
      simp_rw [hzsq, ← Finset.mul_sum, hxs]
    rw [hs] at hc
    exact hc
  have hsum0 : 0 ≤ ∑ i, z i := Finset.sum_nonneg (fun i _ => hz i)
  have hsum : (∑ i, z i) ≤ K/4 := by
    have hg : 64*q*e^2*n ≤ K := hgap
    have hmult := mul_le_mul_of_nonneg_left hg hK0.le
    nlinarith
  have hys := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hy i)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, hxs] at hys
  have hm := mul_le_mul_of_nonneg_left hsum hn
  apply (div_le_iff₀ hK0).2
  change (2:ℝ) ≤ K at hK
  nlinarith [mul_nonneg hn (by linarith : 0 ≤ K-2)]

def gap (K q n : ℝ) := min (1/4:ℝ) (Real.sqrt (K/(64*q*n)))

theorem gap_properties (K q n : ℝ) (hK : 0 < K) (hq : 0 < q) (hn : 0 < n) :
    0 ≤ gap K q n ∧ gap K q n ≤ 1/4 ∧ 64*q*(gap K q n)^2*n ≤ K := by
  have hd : 0 < 64*q*n := by positivity
  have hx := Real.sq_sqrt (div_pos hK hd).le
  have he : 0 ≤ gap K q n := le_min (by norm_num) (Real.sqrt_nonneg _)
  have hu : gap K q n ≤ Real.sqrt (K/(64*q*n)) := min_le_right _ _
  have hs : (gap K q n)^2 ≤ K/(64*q*n) := by nlinarith [Real.sqrt_nonneg (K/(64*q*n))]
  have hc := (le_div_iff₀ hd).mp hs
  exact ⟨he, min_le_left _ _, by nlinarith⟩

theorem clipped_information_rate (K q n : ℝ) (hK : 0 < K) (hq : 0 < q) (hn : 0 < n) :
    (1/32:ℝ)*min n (Real.sqrt (K*n/q)) ≤ gap K q n*n/4 := by
  have hd : 0 < 64*q*n := by positivity
  have hx := Real.sq_sqrt (div_pos hK hd).le
  have hy := Real.sq_sqrt (div_pos (mul_pos hK hn) hq).le
  have heq : n*Real.sqrt (K/(64*q*n))=Real.sqrt (K*n/q)/8 := by
    have ha : 0 ≤ n*Real.sqrt (K/(64*q*n)) := by positivity
    have hb : 0 ≤ Real.sqrt (K*n/q)/8 := by positivity
    have hsq : (n*Real.sqrt (K/(64*q*n)))^2=(Real.sqrt (K*n/q)/8)^2 := by
      rw [mul_pow, hx, div_pow, hy]
      field_simp
      ring
    nlinarith
  unfold gap
  rcases le_total (1/4:ℝ) (Real.sqrt (K/(64*q*n))) with h | h
  · rw [min_eq_left h]
    have hm := min_le_left n (Real.sqrt (K*n/q))
    nlinarith
  · rw [min_eq_right h]
    have hm := min_le_right n (Real.sqrt (K*n/q))
    nlinarith

theorem information_lower_from_counts {I : Type*} [Fintype I]
    (x y : I → ℝ) (n q : ℝ)
    (hK : (2:ℝ) ≤ Fintype.card I) (hn : 0 < n) (hq : 0 < q)
    (hx : ∀ i, 0 ≤ x i) (hxs : ∑ i, x i=n)
    (hy : ∀ i, y i ≤ x i+n*Real.sqrt (4*q*(gap (Fintype.card I) q n)^2*x i)) :
    (1/32:ℝ)*min n (Real.sqrt ((Fintype.card I)*n/q)) ≤
      gap (Fintype.card I) q n*(n-(∑ i, y i)/(Fintype.card I:ℝ)) := by
  have hK0 : (0:ℝ) < Fintype.card I := by linarith
  have hg := gap_properties (Fintype.card I) q n hK0 hq hn
  have hc := average_count x y n q (gap (Fintype.card I) q n) hK hn.le hq.le hg.1 hx hxs hy hg.2.2
  have hr := clipped_information_rate (Fintype.card I) q n hK0 hq hn
  have hm := mul_le_mul_of_nonneg_left hc hg.1
  nlinarith

end DRGPR.InformationRate
#print axioms DRGPR.InformationRate.average_count
#print axioms DRGPR.InformationRate.gap_properties
#print axioms DRGPR.InformationRate.clipped_information_rate
#print axioms DRGPR.InformationRate.information_lower_from_counts
