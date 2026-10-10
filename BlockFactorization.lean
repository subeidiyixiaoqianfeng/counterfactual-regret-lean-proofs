import ObliviousFactorization

/- Factorization at block boundaries. The response can depend on the current
fixed block table because it is the law of an entire within-block execution.
Non-anticipation inside that execution must be proved by its construction. -/
noncomputable section
open scoped BigOperators
namespace DRGPR.BlockFactorization
open SupportedInformation FiniteSimulation ObliviousFactorization
variable {E A : Type} [Fintype E] [Fintype A]

def kernel (env : (n : ℕ) → Hist E n → E → ℝ)
    (response : (n : ℕ) → Hist E n → Hist A n → E → A → ℝ)
    (n : ℕ) (h : Hist (E × A) n) (x : E × A) : ℝ :=
  env n (project Prod.fst n h) x.1 *
    response n (project Prod.fst n h) (project Prod.snd n h) x.1 x.2

def weight (response : (n : ℕ) → Hist E n → Hist A n → E → A → ℝ) :
    (n : ℕ) → Hist E n → Hist A n → ℝ
  | 0, _, _ => 1
  | n+1, e, a => weight response n e.1 a.1 * response n e.1 a.1 e.2 a.2

theorem normalized (response : (n : ℕ) → Hist E n → Hist A n → E → A → ℝ)
    (hr : ∀ n e a x, ∑ y, response n e a x y=1) :
    ∀ n e, ∑ a, weight response n e a=1 := by
  intro n
  induction n with
  | zero => intro e; simp [Hist,weight]
  | succ n ih =>
    intro e
    change (∑ a : Hist A n × A, weight response n e.1 a.1*response n e.1 a.1 e.2 a.2)=1
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum,hr,mul_one]
    exact ih e.1

theorem weight_nonneg (response : (n : ℕ) → Hist E n → Hist A n → E → A → ℝ)
    (hr : ∀ n e a x y, 0 ≤ response n e a x y) :
    ∀ n e a, 0 ≤ weight response n e a := by
  intro n
  induction n with
  | zero => intro e a; exact zero_le_one
  | succ n ih => intro e a; exact mul_nonneg (ih e.1 a.1) (hr n e.1 a.1 e.2 a.2)

theorem kernel_normalized (env : (n : ℕ) → Hist E n → E → ℝ)
    (response : (n : ℕ) → Hist E n → Hist A n → E → A → ℝ)
    (he : ∀ n e, ∑ x, env n e x=1)
    (hr : ∀ n e a x, ∑ y, response n e a x y=1) :
    ∀ n h, ∑ x, kernel env response n h x=1 := by
  intro n h
  unfold kernel
  rw [Fintype.sum_prod_type]
  simp only [← Finset.mul_sum,hr,mul_one,he]

theorem factorization (env : (n : ℕ) → Hist E n → E → ℝ)
    (response : (n : ℕ) → Hist E n → Hist A n → E → A → ℝ) :
    ∀ n e a, pathLaw (kernel env response) n (zip n e a)=
      pathLaw env n e*weight response n e a := by
  intro n
  induction n with
  | zero => intro e a; simp [pathLaw,weight]
  | succ n ih =>
    intro e a
    change (pathLaw (kernel env response) n (zip n e.1 a.1)*
      (env n (project Prod.fst n (zip n e.1 a.1)) e.2 *
        response n (project Prod.fst n (zip n e.1 a.1))
          (project Prod.snd n (zip n e.1 a.1)) e.2 a.2)) =
      (pathLaw env n e.1*env n e.1 e.2)*(weight response n e.1 a.1*response n e.1 a.1 e.2 a.2)
    rw [ih,(project_zip n e.1 a.1).1,(project_zip n e.1 a.1).2]
    ring

theorem expectation_factorization (env : (n : ℕ) → Hist E n → E → ℝ)
    (response : (n : ℕ) → Hist E n → Hist A n → E → A → ℝ)
    (n : ℕ) (payoff : Hist (E × A) n → ℝ) :
    (∑ h, pathLaw (kernel env response) n h*payoff h)=
      ∑ e, pathLaw env n e*(∑ a, weight response n e a*payoff (zip n e a)) := by
  rw [sum_zip]
  simp_rw [factorization,Finset.mul_sum,mul_assoc]

end DRGPR.BlockFactorization
#print axioms DRGPR.BlockFactorization.normalized
#print axioms DRGPR.BlockFactorization.weight_nonneg
#print axioms DRGPR.BlockFactorization.kernel_normalized
#print axioms DRGPR.BlockFactorization.factorization
#print axioms DRGPR.BlockFactorization.expectation_factorization
