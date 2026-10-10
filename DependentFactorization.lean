import DependentBlocks
import BlockFactorization

noncomputable section
open scoped BigOperators
namespace DRGPR.DependentFactorization
open DependentBlocks
variable {E A Z : ℕ → Type}

def project (f : ∀ r, E r → A r) : (n : ℕ) → History E n → History A n
  | 0, _ => ()
  | n+1, h => (project f n h.1,f n h.2)

def zip : (n : ℕ) → History E n → History A n → History (fun r => E r × A r) n
  | 0, _, _ => ()
  | n+1, e, a => (zip n e.1 a.1,(e.2,a.2))

theorem zip_project : ∀ n (h : History (fun r => E r × A r) n),
    zip n (project (fun _ => Prod.fst) n h) (project (fun _ => Prod.snd) n h)=h := by
  intro n
  induction n with
  | zero => intro h; cases h; rfl
  | succ n ih =>
    intro h
    change (zip n (project (fun _ => Prod.fst) n h.1)
      (project (fun _ => Prod.snd) n h.1),(h.2.1,h.2.2))=h
    rw [ih]
    rfl

theorem project_zip : ∀ n (e : History E n) (a : History A n),
    project (fun _ => Prod.fst) n (zip n e a)=e ∧
      project (fun _ => Prod.snd) n (zip n e a)=a := by
  intro n
  induction n with
  | zero => intro e a; cases e; cases a; exact ⟨rfl,rfl⟩
  | succ n ih =>
    intro e a
    have hh := ih e.1 a.1
    constructor
    · change (project (fun _ => Prod.fst) n (zip n e.1 a.1),e.2)=e
      rw [hh.1]
      rfl
    · change (project (fun _ => Prod.snd) n (zip n e.1 a.1),a.2)=a
      rw [hh.2]
      rfl

def splitEquiv (n : ℕ) : History (fun r => E r × A r) n ≃ History E n × History A n where
  toFun h := (project (fun _ => Prod.fst) n h,project (fun _ => Prod.snd) n h)
  invFun h := zip n h.1 h.2
  left_inv := zip_project n
  right_inv h := Prod.ext (project_zip n h.1 h.2).1 (project_zip n h.1 h.2).2

theorem sum_zip [∀ r, Fintype (E r)] [∀ r, Fintype (A r)]
    (n : ℕ) (f : History (fun r => E r × A r) n → ℝ) :
    (∑ h, f h)=∑ e, ∑ a, f (zip n e a) := by
  calc
    _ = ∑ h : History E n × History A n, f (zip n h.1 h.2) :=
      Fintype.sum_equiv (splitEquiv n) _ _ (fun h => by simp [splitEquiv,zip_project])
    _ = _ := Fintype.sum_prod_type _

def kernel (env : (n : ℕ) → History E n → E n → ℝ)
    (response : (n : ℕ) → History E n → History A n → E n → A n → ℝ)
    (n : ℕ) (h : History (fun r => E r × A r) n) (x : E n × A n) : ℝ :=
  env n (project (fun _ => Prod.fst) n h) x.1 *
    response n (project (fun _ => Prod.fst) n h) (project (fun _ => Prod.snd) n h) x.1 x.2

def weight (response : (n : ℕ) → History E n → History A n → E n → A n → ℝ) :
    (n : ℕ) → History E n → History A n → ℝ
  | 0, _, _ => 1
  | n+1, e, a => weight response n e.1 a.1 * response n e.1 a.1 e.2 a.2

theorem normalized [∀ r, Fintype (A r)]
    (response : (n : ℕ) → History E n → History A n → E n → A n → ℝ)
    (hr : ∀ n e a x, ∑ y, response n e a x y=1) :
    ∀ n e, ∑ a, weight response n e a=1 := by
  intro n
  induction n with
  | zero => intro e; simp [History,weight]
  | succ n ih =>
    intro e
    change (∑ a : History A n × A n, weight response n e.1 a.1*response n e.1 a.1 e.2 a.2)=1
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum,hr,mul_one]
    exact ih e.1

theorem weight_nonneg (response : (n : ℕ) → History E n → History A n → E n → A n → ℝ)
    (hr : ∀ n e a x y, 0 ≤ response n e a x y) :
    ∀ n e a, 0 ≤ weight response n e a := by
  intro n
  induction n with
  | zero => intro e a; exact zero_le_one
  | succ n ih => intro e a; exact mul_nonneg (ih e.1 a.1) (hr n e.1 a.1 e.2 a.2)

theorem kernel_normalized [∀ r, Fintype (E r)] [∀ r, Fintype (A r)]
    (env : (n : ℕ) → History E n → E n → ℝ)
    (response : (n : ℕ) → History E n → History A n → E n → A n → ℝ)
    (he : ∀ n e, ∑ x, env n e x=1)
    (hr : ∀ n e a x, ∑ y, response n e a x y=1) :
    ∀ n h, ∑ x, kernel env response n h x=1 := by
  intro n h
  unfold kernel
  rw [Fintype.sum_prod_type]
  simp only [← Finset.mul_sum,hr,mul_one,he]

theorem factorization (env : (n : ℕ) → History E n → E n → ℝ)
    (response : (n : ℕ) → History E n → History A n → E n → A n → ℝ) :
    ∀ n e a, law (kernel env response) n (zip n e a)=law env n e*weight response n e a := by
  intro n
  induction n with
  | zero => intro e a; simp [law,weight]
  | succ n ih =>
    intro e a
    change (law (kernel env response) n (zip n e.1 a.1)*
      (env n (project (fun _ => Prod.fst) n (zip n e.1 a.1)) e.2 *
        response n (project (fun _ => Prod.fst) n (zip n e.1 a.1))
          (project (fun _ => Prod.snd) n (zip n e.1 a.1)) e.2 a.2)) =
      (law env n e.1*env n e.1 e.2)*(weight response n e.1 a.1*response n e.1 a.1 e.2 a.2)
    rw [ih,(project_zip n e.1 a.1).1,(project_zip n e.1 a.1).2]
    ring

theorem expectation_factorization [∀ r, Fintype (E r)] [∀ r, Fintype (A r)]
    (env : (n : ℕ) → History E n → E n → ℝ)
    (response : (n : ℕ) → History E n → History A n → E n → A n → ℝ)
    (n : ℕ) (payoff : History (fun r => E r × A r) n → ℝ) :
    (∑ h, law (kernel env response) n h*payoff h)=
      ∑ e, law env n e*(∑ a, weight response n e a*payoff (zip n e a)) := by
  rw [sum_zip]
  simp_rw [factorization,Finset.mul_sum,mul_assoc]

end DRGPR.DependentFactorization
#print axioms DRGPR.DependentFactorization.zip_project
#print axioms DRGPR.DependentFactorization.project_zip
#print axioms DRGPR.DependentFactorization.sum_zip
#print axioms DRGPR.DependentFactorization.normalized
#print axioms DRGPR.DependentFactorization.weight_nonneg
#print axioms DRGPR.DependentFactorization.kernel_normalized
#print axioms DRGPR.DependentFactorization.factorization
#print axioms DRGPR.DependentFactorization.expectation_factorization
