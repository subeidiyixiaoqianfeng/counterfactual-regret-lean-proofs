import FiniteTesting

/-! Relative entropy on finite distributions with zero-probability histories.
Absolute continuity is explicit, so Real.log 0 never silently substitutes
for infinite KL. -/
noncomputable section
open scoped BigOperators
namespace DRGPR.SupportedInformation
open DRGPR.FiniteInformation

theorem chain_rule {I J : Type*} [Fintype I] [Fintype J]
    (p q : I → ℝ) (k l : I → J → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 < p i → 0 < q i)
    (hk : ∀ i j, 0 ≤ k i j) (hl : ∀ i j, 0 < k i j → 0 < l i j)
    (hks : ∀ i, ∑ j, k i j=1) :
    divergence (fun s : I × J => p s.1*k s.1 s.2)
      (fun s : I × J => q s.1*l s.1 s.2) =
      divergence p q + ∑ i, p i*divergence (k i) (l i) := by
  unfold divergence
  rw [Fintype.sum_prod_type, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hpi : p i=0
  · simp [hpi]
  have hpp : 0 < p i := lt_of_le_of_ne (hp i) (Ne.symm hpi)
  have hterm (j : J) : p i*k i j*Real.log ((p i*k i j)/(q i*l i j)) =
      p i*k i j*Real.log (p i/q i)+p i*(k i j*Real.log (k i j/l i j)) := by
    by_cases hkj : k i j=0
    · simp [hkj]
    have hkp : 0 < k i j := lt_of_le_of_ne (hk i j) (Ne.symm hkj)
    rw [product_log (p i) (q i) (k i j) (l i j) hpp (hq i hpp) hkp (hl i j hkp)]
    ring
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hfirst : (∑ j, p i*k i j*Real.log (p i/q i))=p i*Real.log (p i/q i) := by
    calc
      _ = (p i*Real.log (p i/q i))*(∑ j, k i j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = _ := by rw [hks]; ring
  rw [hfirst]

theorem shared_kernel_cancels {I J : Type*} [Fintype I] [Fintype J]
    (p q : I → ℝ) (k : I → J → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 < p i → 0 < q i)
    (hk : ∀ i j, 0 ≤ k i j) (hks : ∀ i, ∑ j, k i j=1) :
    divergence (fun s : I × J => p s.1*k s.1 s.2)
      (fun s : I × J => q s.1*k s.1 s.2) = divergence p q := by
  rw [chain_rule p q k k hp hq hk (fun _ _ h => h) hks]
  have hz (i : I) : divergence (k i) (k i)=0 := by
    apply Finset.sum_eq_zero
    intro j _
    by_cases h : k i j=0 <;> simp [h]
  simp [hz]

def Hist (A : Type) : ℕ → Type
  | 0 => Unit
  | n+1 => Hist A n × A

instance histFintype {A : Type} [Fintype A] : (n : ℕ) → Fintype (Hist A n)
  | 0 => inferInstanceAs (Fintype Unit)
  | n+1 => by
      letI : Fintype (Hist A n) := histFintype n
      exact inferInstanceAs (Fintype (Hist A n × A))

def pathLaw {A : Type} (k : (n : ℕ) → Hist A n → A → ℝ) :
    (n : ℕ) → Hist A n → ℝ
  | 0, _ => 1
  | n+1, h => pathLaw k n h.1*k n h.1 h.2

theorem pathLaw_nonneg {A : Type} (k : (n : ℕ) → Hist A n → A → ℝ)
    (hk : ∀ n h a, 0 ≤ k n h a) : ∀ n h, 0 ≤ pathLaw k n h := by
  intro n
  induction n with
  | zero => intro h; exact zero_le_one
  | succ n ih => intro h; exact mul_nonneg (ih h.1) (hk n h.1 h.2)

theorem pathLaw_normalized {A : Type} [Fintype A]
    (k : (n : ℕ) → Hist A n → A → ℝ)
    (hk : ∀ n h, ∑ a, k n h a=1) : ∀ n, ∑ h, pathLaw k n h=1 := by
  intro n
  induction n with
  | zero => simp [Hist, pathLaw]
  | succ n ih =>
    change (∑ h : Hist A n × A, pathLaw k n h.1*k n h.1 h.2)=1
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, hk, mul_one]
    exact ih

theorem pathLaw_support {A : Type}
    (k l : (n : ℕ) → Hist A n → A → ℝ)
    (hk : ∀ n h a, 0 ≤ k n h a)
    (hl : ∀ n h a, 0 < k n h a → 0 < l n h a) :
    ∀ n h, 0 < pathLaw k n h → 0 < pathLaw l n h := by
  intro n
  induction n with
  | zero => intro h _; exact zero_lt_one
  | succ n ih =>
    intro h hp
    change 0 < pathLaw k n h.1*k n h.1 h.2 at hp
    have h₁ : 0 < pathLaw k n h.1 := pos_of_mul_pos_left hp (hk n h.1 h.2)
    have h₂ : 0 < k n h.1 h.2 := pos_of_mul_pos_right hp (pathLaw_nonneg k hk n h.1)
    exact mul_pos (ih h.1 h₁) (hl n h.1 h.2 h₂)

theorem adaptive_chain {A : Type} [Fintype A]
    (k l : (n : ℕ) → Hist A n → A → ℝ)
    (hk : ∀ n h a, 0 ≤ k n h a)
    (hl : ∀ n h a, 0 < k n h a → 0 < l n h a)
    (hks : ∀ n h, ∑ a, k n h a=1) (N : ℕ) :
    divergence (pathLaw k N) (pathLaw l N) =
      ∑ n ∈ Finset.range N, ∑ h, pathLaw k n h*divergence (k n h) (l n h) := by
  induction N with
  | zero => simp [divergence, Hist, pathLaw]
  | succ n ih =>
    change divergence (fun h : Hist A n × A => pathLaw k n h.1*k n h.1 h.2)
      (fun h : Hist A n × A => pathLaw l n h.1*l n h.1 h.2) = _
    rw [chain_rule _ _ _ _ (pathLaw_nonneg k hk n) (pathLaw_support k l hk hl n)
      (hk n) (hl n) (hks n), ih, Finset.sum_range_succ]

def cumulative {A : Type} (c : (n : ℕ) → Hist A n → A → ℝ) :
    (n : ℕ) → Hist A n → ℝ
  | 0, _ => 0
  | n+1, h => cumulative c n h.1+c n h.1 h.2

theorem expected_cumulative {A : Type} [Fintype A]
    (k c : (n : ℕ) → Hist A n → A → ℝ)
    (hks : ∀ n h, ∑ a, k n h a=1) (N : ℕ) :
    (∑ h, pathLaw k N h*cumulative c N h) =
      ∑ n ∈ Finset.range N, ∑ h, pathLaw k n h*(∑ a, k n h a*c n h a) := by
  induction N with
  | zero => simp [Hist, pathLaw, cumulative]
  | succ n ih =>
    change (∑ h : Hist A n × A, (pathLaw k n h.1*k n h.1 h.2)*
      (cumulative c n h.1+c n h.1 h.2)) = _
    rw [Fintype.sum_prod_type, Finset.sum_range_succ, ← ih]
    have hterm (h : Hist A n) :
        (∑ a, (pathLaw k n h*k n h a)*(cumulative c n h+c n h a)) =
        pathLaw k n h*cumulative c n h+pathLaw k n h*(∑ a, k n h a*c n h a) := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib]
      have hfirst : (∑ a, pathLaw k n h*k n h a*cumulative c n h)=pathLaw k n h*cumulative c n h := by
        calc
          _ = (pathLaw k n h*cumulative c n h)*(∑ a, k n h a) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro a _
            ring
          _ = _ := by rw [hks]; ring
      rw [hfirst, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro a _
      ring
    simp_rw [hterm]
    rw [Finset.sum_add_distrib]

end DRGPR.SupportedInformation
#print axioms DRGPR.SupportedInformation.chain_rule
#print axioms DRGPR.SupportedInformation.shared_kernel_cancels
#print axioms DRGPR.SupportedInformation.pathLaw_nonneg
#print axioms DRGPR.SupportedInformation.pathLaw_normalized
#print axioms DRGPR.SupportedInformation.pathLaw_support
#print axioms DRGPR.SupportedInformation.adaptive_chain
#print axioms DRGPR.SupportedInformation.expected_cumulative
