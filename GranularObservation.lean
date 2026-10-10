import TableDistribution
import FiniteController

noncomputable section
open scoped BigOperators
namespace DRGPR.GranularObservation
open TableDistribution ErasedBandit
variable {J : Type} [Fintype J] [DecidableEq J]

theorem pair_expectation (p : J → ℝ) (i j : J) (hij : i ≠ j) (f g : Bool → ℝ) :
    (∑ x, row p x*(f (x i)*g (x j))) =
      (∑ b, bernoulli (p i) b*f b)*(∑ b, bernoulli (p j) b*g b) := by
  let aug := fun k b => bernoulli (p k) b*(if k=i then f b else 1)*(if k=j then g b else 1)
  have hp (x : J → Bool) : row p x*(f (x i)*g (x j)) = ∏ k, aug k (x k) := by
    dsimp [row,aug]
    rw [Finset.prod_mul_distrib,Finset.prod_mul_distrib]
    simp
    ring
  simp_rw [hp]
  rw [← Fintype.prod_sum]
  have hs (k : J) : (∑ b, aug k b) =
      (if k=i then (∑ b, bernoulli (p i) b*f b) else 1)*
      (if k=j then (∑ b, bernoulli (p j) b*g b) else 1) := by
    by_cases hi : k=i
    · subst k; simp [aug,hij]
    · by_cases hj : k=j
      · subst k; simp [aug,Ne.symm hij]
      · simp [aug,hi,hj,bernoulli,Fintype.sum_bool]
  simp_rw [hs]
  rw [Finset.prod_mul_distrib]
  simp

def observed (q : ℝ) (b : Bool) : ℝ := if b then 0 else 1/q
def score (q : ℝ) (l : J → ℝ) (x : J → Bool) : ℝ := ∑ t, l t*observed q (x t)

theorem first_coordinate (q : ℝ) (hq : q ≠ 0) (t : J) :
    (∑ x, row (fun _ : J => q) x*observed q (x t)) = 1 := by
  rw [coordinate_expectation]
  simp [observed,bernoulli,Fintype.sum_bool,hq]

theorem coordinate_second (q : ℝ) (hq : q ≠ 0) (t : J) :
    (∑ x, row (fun _ : J => q) x*(observed q (x t))^2) = 1/q := by
  rw [coordinate_expectation _ t (fun b => (observed q b)^2)]
  simp [observed,bernoulli,Fintype.sum_bool]
  field_simp
  ring

theorem cross_coordinate (q : ℝ) (hq : q ≠ 0) (s t : J) (hst : s ≠ t) :
    (∑ x, row (fun _ : J => q) x*(observed q (x s)*observed q (x t))) = 1 := by
  rw [pair_expectation _ s t hst]
  simp [observed,bernoulli,Fintype.sum_bool,hq]

theorem score_mean (q : ℝ) (hq : q ≠ 0) (l : J → ℝ) :
    (∑ x, row (fun _ : J => q) x*score q l x) = ∑ t, l t := by
  unfold score
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  calc
    _ = l t*(∑ x, row (fun _ : J => q) x*observed q (x t)) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro x _; ring
    _ = _ := by rw [first_coordinate q hq]; ring

theorem score_second (q : ℝ) (hq : q ≠ 0) (l : J → ℝ) :
    (∑ x, row (fun _ : J => q) x*(score q l x)^2) =
      (∑ t, l t)^2+(1/q-1)*(∑ t, (l t)^2) := by
  have hex (x : J → Bool) : (score q l x)^2 =
      ∑ s, ∑ t, (l s*l t)*(observed q (x s)*observed q (x t)) := by
    unfold score
    rw [pow_two,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro s _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    ring
  have hpair (s t : J) :
      (∑ x, row (fun _ : J => q) x*((l s*l t)*(observed q (x s)*observed q (x t)))) =
        l s*l t+(if s=t then (1/q-1)*(l s)^2 else 0) := by
    calc
      _ = (l s*l t)*(∑ x, row (fun _ : J => q) x*(observed q (x s)*observed q (x t))) := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro x _; ring
      _ = _ := by
        by_cases hst : s=t
        · subst t
          simp only [ite_true,← pow_two,coordinate_second q hq]
          ring
        · rw [cross_coordinate q hq s t hst,if_neg hst]
          ring
  simp_rw [hex,Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (f:=fun x t => row (fun _ : J => q) x*((l _*l t)*(observed q (x _)*observed q (x t))))]
  simp_rw [hpair]
  simp only [Finset.sum_add_distrib]
  simp
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul]
  ring

theorem score_nonneg (q : ℝ) (hq : 0 ≤ q) (l : J → ℝ) (hl : ∀ t, 0 ≤ l t) (x : J → Bool) :
    0 ≤ score q l x := by
  apply Finset.sum_nonneg
  intro t _
  apply mul_nonneg (hl t)
  unfold observed
  split_ifs <;> positivity

theorem score_bounded (q : ℝ) (hq : 0 < q) (l : J → ℝ) (hl : ∀ t, 0 ≤ l t)
    (hl1 : ∀ t, l t ≤ 1) (x : J → Bool) : score q l x ≤ (Fintype.card J:ℝ)/q := by
  calc
    _ ≤ ∑ t : J, 1/q := by
      apply Finset.sum_le_sum
      intro t _
      unfold observed
      split_ifs
      · simp; positivity
      · simpa using mul_le_mul_of_nonneg_right (hl1 t) (by positivity : 0 ≤ 1/q)
    _ = _ := by simp [div_eq_mul_inv]

theorem score_second_bound (q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1)
    (l : J → ℝ) (hl : ∀ t, 0 ≤ l t) (hl1 : ∀ t, l t ≤ 1) :
    (∑ x, row (fun _ : J => q) x*(score q l x)^2) ≤
      (Fintype.card J:ℝ)^2+(Fintype.card J:ℝ)/q := by
  rw [score_second q hq.ne']
  have hsum0 : 0 ≤ ∑ t, l t := Finset.sum_nonneg (fun t _ => hl t)
  have hsum : (∑ t, l t) ≤ Fintype.card J := by
    calc
      _ ≤ ∑ _t : J, (1:ℝ) := Finset.sum_le_sum (fun t _ => hl1 t)
      _ = _ := by simp
  have hsquare : (∑ t, (l t)^2) ≤ Fintype.card J := by
    calc
      _ ≤ ∑ _t : J, (1:ℝ) := Finset.sum_le_sum (fun t _ => by nlinarith [hl t,hl1 t])
      _ = _ := by simp
  have hc : 0 ≤ 1/q-1 := by
    have h : (1:ℝ) ≤ 1/q := (le_div_iff₀ hq).2 (by simpa using hq1)
    linarith
  have hm := mul_le_mul_of_nonneg_left hsquare hc
  have hh := DRGPR.square_bounded _ _ hsum0 hsum
  have hn : (0:ℝ) ≤ Fintype.card J := Nat.cast_nonneg _
  have hdiv : (1/q-1)*(Fintype.card J:ℝ) = (Fintype.card J:ℝ)/q-Fintype.card J := by ring
  rw [hdiv] at hm
  linarith

end DRGPR.GranularObservation
#print axioms DRGPR.GranularObservation.pair_expectation
#print axioms DRGPR.GranularObservation.first_coordinate
#print axioms DRGPR.GranularObservation.coordinate_second
#print axioms DRGPR.GranularObservation.cross_coordinate
#print axioms DRGPR.GranularObservation.score_mean
#print axioms DRGPR.GranularObservation.score_second
#print axioms DRGPR.GranularObservation.score_nonneg
#print axioms DRGPR.GranularObservation.score_bounded
#print axioms DRGPR.GranularObservation.score_second_bound
