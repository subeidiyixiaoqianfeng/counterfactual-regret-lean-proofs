import TunedPhase

noncomputable section
open scoped BigOperators
namespace DRGPR.DependentBlocks

def History (E : ℕ → Type) : ℕ → Type
  | 0 => Unit
  | n+1 => History E n × E n

instance historyFintype (E : ℕ → Type) [∀ n, Fintype (E n)] : (n : ℕ) → Fintype (History E n)
  | 0 => inferInstanceAs (Fintype Unit)
  | n+1 => by
    letI : Fintype (History E n) := historyFintype E n
    exact inferInstanceAs (Fintype (History E n × E n))

def law {E : ℕ → Type} (k : (n : ℕ) → History E n → E n → ℝ) :
    (n : ℕ) → History E n → ℝ
  | 0, _ => 1
  | n+1, h => law k n h.1*k n h.1 h.2

def total {E : ℕ → Type} (c : (n : ℕ) → History E n → E n → ℝ) :
    (n : ℕ) → History E n → ℝ
  | 0, _ => 0
  | n+1, h => total c n h.1+c n h.1 h.2

theorem normalized {E : ℕ → Type} [∀ n, Fintype (E n)]
    (k : (n : ℕ) → History E n → E n → ℝ)
    (hk : ∀ n h, ∑ a, k n h a=1) : ∀ n, ∑ h, law k n h=1 := by
  intro n
  induction n with
  | zero => simp [History,law]
  | succ n ih =>
    change (∑ h : History E n × E n, law k n h.1*k n h.1 h.2)=1
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum,hk,mul_one]
    exact ih

theorem nonneg {E : ℕ → Type}
    (k : (n : ℕ) → History E n → E n → ℝ)
    (hk : ∀ n h a, 0 ≤ k n h a) : ∀ n h, 0 ≤ law k n h := by
  intro n
  induction n with
  | zero => intro h; exact zero_le_one
  | succ n ih => intro h; exact mul_nonneg (ih h.1) (hk n h.1 h.2)

theorem expected_step {E : ℕ → Type} [∀ n, Fintype (E n)]
    (k c : (n : ℕ) → History E n → E n → ℝ)
    (hk : ∀ n h, ∑ a, k n h a=1) (n : ℕ) :
    (∑ h, law k (n+1) h*total c (n+1) h)=
      (∑ h, law k n h*total c n h)+
      ∑ h, law k n h*(∑ a, k n h a*c n h a) := by
  change (∑ h : History E n × E n,
    (law k n h.1*k n h.1 h.2)*(total c n h.1+c n h.1 h.2))=_
  rw [Fintype.sum_prod_type,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro h _
  simp only [mul_add,Finset.sum_add_distrib]
  have he : (∑ a, (law k n h*k n h a)*total c n h)=law k n h*total c n h := by
    rw [← Finset.sum_mul,← Finset.mul_sum,hk,mul_one]
  rw [he]
  congr 1
  simp only [Finset.mul_sum,mul_assoc]

theorem expected_total_le {E : ℕ → Type} [∀ n, Fintype (E n)]
    (k c : (n : ℕ) → History E n → E n → ℝ)
    (hk : ∀ n h a, 0 ≤ k n h a) (hk1 : ∀ n h, ∑ a, k n h a=1)
    (bound : ℕ → ℝ) (hc : ∀ n h, (∑ a, k n h a*c n h a) ≤ bound n) :
    ∀ N, (∑ h, law k N h*total c N h) ≤ ∑ n ∈ Finset.range N, bound n := by
  intro N
  induction N with
  | zero => simp [History,law,total]
  | succ N ih =>
    rw [expected_step k c hk1,Finset.sum_range_succ]
    apply add_le_add ih
    calc
      _ ≤ ∑ h, law k N h*bound N := Finset.sum_le_sum (fun h _ =>
        mul_le_mul_of_nonneg_left (hc N h) (nonneg k hk N h))
      _ = _ := by rw [← Finset.sum_mul,normalized k hk1,one_mul]

theorem subtract_deterministic {E : ℕ → Type}
    (c : (n : ℕ) → History E n → E n → ℝ) (v : ℕ → ℝ) :
    ∀ n h, total (fun r hist a => c r hist a-v r) n h=
      total c n h-∑ r ∈ Finset.range n, v r := by
  intro n
  induction n with
  | zero => intro h; simp [total]
  | succ n ih =>
    intro h
    rw [total,total,ih,Finset.sum_range_succ]
    ring

end DRGPR.DependentBlocks
#print axioms DRGPR.DependentBlocks.normalized
#print axioms DRGPR.DependentBlocks.nonneg
#print axioms DRGPR.DependentBlocks.expected_step
#print axioms DRGPR.DependentBlocks.expected_total_le
#print axioms DRGPR.DependentBlocks.subtract_deterministic
