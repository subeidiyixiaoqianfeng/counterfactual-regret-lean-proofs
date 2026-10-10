import DRGPR

/-! Finite relative-entropy identities used before the lower-bound count argument.
Positive-density assumptions are explicit. No Pinsker or minimax theorem is
assumed to have been proved by these identities. -/
noncomputable section
open scoped BigOperators
namespace DRGPR.FiniteInformation

def divergence {I : Type*} [Fintype I] (p q : I → ℝ) : ℝ :=
  ∑ i, p i * Real.log (p i/q i)

theorem product_log (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hd : 0 < d) :
    Real.log ((a*c)/(b*d)) = Real.log (a/b)+Real.log (c/d) := by
  rw [show (a*c)/(b*d)=(a/b)*(c/d) by field_simp <;> ring]
  exact Real.log_mul (div_pos ha hb).ne' (div_pos hc hd).ne'

theorem chain_rule {I J : Type*} [Fintype I] [Fintype J]
    (p q : I → ℝ) (k l : I → J → ℝ)
    (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i)
    (hk : ∀ i j, 0 < k i j) (hl : ∀ i j, 0 < l i j)
    (hks : ∀ i, ∑ j, k i j=1) :
    divergence (fun s : I × J => p s.1*k s.1 s.2)
      (fun s : I × J => q s.1*l s.1 s.2)
      = divergence p q + ∑ i, p i*divergence (k i) (l i) := by
  unfold divergence
  rw [Fintype.sum_prod_type, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hlog (j : J) := product_log (p i) (q i) (k i j) (l i j)
    (hp i) (hq i) (hk i j) (hl i j)
  simp_rw [hlog, mul_add]
  rw [Finset.sum_add_distrib]
  have hfirst : (∑ j, p i*k i j*Real.log (p i/q i))=p i*Real.log (p i/q i) := by
    calc
      _ = (p i*Real.log (p i/q i))*(∑ j, k i j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = _ := by rw [hks]; ring
  rw [hfirst, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem shared_kernel_cancels {I J : Type*} [Fintype I] [Fintype J]
    (p q : I → ℝ) (k : I → J → ℝ)
    (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i)
    (hk : ∀ i j, 0 < k i j) (hks : ∀ i, ∑ j, k i j=1) :
    divergence (fun s : I × J => p s.1*k s.1 s.2)
      (fun s : I × J => q s.1*k s.1 s.2) = divergence p q := by
  rw [chain_rule p q k k hp hq hk hk hks]
  simp [divergence, fun i j => (hk i j).ne']

def erased {I : Type*} (r : ℝ) (p : I → ℝ) : Option I → ℝ
  | none => 1-r
  | some i => r*p i

theorem erasure_factor {I : Type*} [Fintype I]
    (p q : I → ℝ) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) :
    divergence (erased r p) (erased r q) = r*divergence p q := by
  unfold divergence
  rw [Fintype.sum_option]
  simp only [erased]
  have hnone : (1-r)*Real.log ((1-r)/(1-r))=0 := by
    by_cases he : r=1
    · simp [he]
    · have hn : 1-r ≠ 0 := sub_ne_zero.mpr (Ne.symm he)
      simp [hn]
  rw [hnone, zero_add, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_div_mul_left _ _ hr.ne']
  ring

end DRGPR.FiniteInformation

#print axioms DRGPR.FiniteInformation.product_log
#print axioms DRGPR.FiniteInformation.chain_rule
#print axioms DRGPR.FiniteInformation.shared_kernel_cancels
#print axioms DRGPR.FiniteInformation.erasure_factor
