import FiniteSimulation

noncomputable section
open scoped BigOperators
namespace DRGPR.ObliviousFactorization
open SupportedInformation FiniteSimulation
variable {E A : Type}

def zip : (n : ℕ) → Hist E n → Hist A n → Hist (E × A) n
  | 0, _, _ => ()
  | n+1, e, a => (zip n e.1 a.1,(e.2,a.2))

theorem zip_project : ∀ n (h : Hist (E × A) n),
    zip n (project Prod.fst n h) (project Prod.snd n h)=h := by
  intro n
  induction n with
  | zero => intro h; cases h; rfl
  | succ n ih =>
    intro h
    change (zip n (project Prod.fst n h.1) (project Prod.snd n h.1),(h.2.1,h.2.2))=h
    rw [ih]
    rfl

theorem project_zip : ∀ n (e : Hist E n) (a : Hist A n),
    project Prod.fst n (zip n e a)=e ∧ project Prod.snd n (zip n e a)=a := by
  intro n
  induction n with
  | zero => intro e a; cases e; cases a; exact ⟨rfl,rfl⟩
  | succ n ih =>
    intro e a
    have h := ih e.1 a.1
    constructor
    · change (project Prod.fst n (zip n e.1 a.1),e.2)=e
      rw [h.1]
      rfl
    · change (project Prod.snd n (zip n e.1 a.1),a.2)=a
      rw [h.2]
      rfl

def splitEquiv (n : ℕ) : Hist (E × A) n ≃ Hist E n × Hist A n where
  toFun h := (project Prod.fst n h,project Prod.snd n h)
  invFun h := zip n h.1 h.2
  left_inv := zip_project n
  right_inv h := Prod.ext (project_zip n h.1 h.2).1 (project_zip n h.1 h.2).2

theorem sum_zip [Fintype E] [Fintype A] (n : ℕ) (f : Hist (E × A) n → ℝ) :
    (∑ h, f h)=∑ e, ∑ a, f (zip n e a) := by
  calc
    _ = ∑ h : Hist E n × Hist A n, f (zip n h.1 h.2) :=
      Fintype.sum_equiv (splitEquiv n) _ _ (fun h => by simp [splitEquiv,zip_project])
    _ = _ := Fintype.sum_prod_type _

def fullKernel
    (env : (n : ℕ) → Hist E n → E → ℝ)
    (choice : (n : ℕ) → Hist E n → Hist A n → A → ℝ)
    (n : ℕ) (h : Hist (E × A) n) (x : E × A) : ℝ :=
  env n (project Prod.fst n h) x.1 * choice n (project Prod.fst n h) (project Prod.snd n h) x.2

/-- Distribution of actions and logging coins with one complete loss table
held fixed. It is recursively normalized and still integrates private coins. -/
def playerWeight (choice : (n : ℕ) → Hist E n → Hist A n → A → ℝ) :
    (n : ℕ) → Hist E n → Hist A n → ℝ
  | 0, _, _ => 1
  | n+1, e, a => playerWeight choice n e.1 a.1 * choice n e.1 a.1 a.2

theorem player_normalized [Fintype A]
    (choice : (n : ℕ) → Hist E n → Hist A n → A → ℝ)
    (hc : ∀ n e h, ∑ a, choice n e h a=1) :
    ∀ n (e : Hist E n), ∑ a, playerWeight choice n e a=1 := by
  intro n
  induction n with
  | zero => intro e; simp [Hist,playerWeight]
  | succ n ih =>
    intro e
    change (∑ a : Hist A n × A, playerWeight choice n e.1 a.1*choice n e.1 a.1 a.2)=1
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum,hc,mul_one]
    exact ih e.1

theorem factorization
    (env : (n : ℕ) → Hist E n → E → ℝ)
    (choice : (n : ℕ) → Hist E n → Hist A n → A → ℝ) :
    ∀ n e a, pathLaw (fullKernel env choice) n (zip n e a)=
      pathLaw env n e*playerWeight choice n e a := by
  intro n
  induction n with
  | zero => intro e a; simp [pathLaw,playerWeight]
  | succ n ih =>
    intro e a
    change (pathLaw (fullKernel env choice) n (zip n e.1 a.1)*
      (env n (project Prod.fst n (zip n e.1 a.1)) e.2 *
       choice n (project Prod.fst n (zip n e.1 a.1)) (project Prod.snd n (zip n e.1 a.1)) a.2)) =
      (pathLaw env n e.1*env n e.1 e.2)*(playerWeight choice n e.1 a.1*choice n e.1 a.1 a.2)
    rw [ih,(project_zip n e.1 a.1).1,(project_zip n e.1 a.1).2]
    ring

theorem expectation_factorization [Fintype E] [Fintype A]
    (env : (n : ℕ) → Hist E n → E → ℝ)
    (choice : (n : ℕ) → Hist E n → Hist A n → A → ℝ)
    (n : ℕ) (payoff : Hist (E × A) n → ℝ) :
    (∑ h, pathLaw (fullKernel env choice) n h*payoff h)=
      ∑ e, pathLaw env n e*(∑ a, playerWeight choice n e a*payoff (zip n e a)) := by
  rw [sum_zip]
  simp_rw [factorization,Finset.mul_sum,mul_assoc]

theorem fixed_instance_from_average {X : Type*} [Fintype X] [Nonempty X]
    (p f : X → ℝ) (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x=1)
    (c : ℝ) (havg : c ≤ ∑ x, p x*f x) : ∃ x, c ≤ f x := by
  by_contra hn
  have hall : ∀ x, f x < c := by simpa using hn
  have hex : ∃ x, 0 < p x := by
    by_contra h
    have hz : ∀ x, p x=0 := fun x => le_antisymm (le_of_not_gt (fun hx => h ⟨x,hx⟩)) (hp x)
    simp [hz] at hp1
  obtain ⟨x,hx⟩ := hex
  have hs : (∑ x, p x*f x) < ∑ x, p x*c := by
    apply Finset.sum_lt_sum
    · intro i _; exact mul_le_mul_of_nonneg_left (hall i).le (hp i)
    · exact ⟨x,Finset.mem_univ x,mul_lt_mul_of_pos_left (hall x) hx⟩
  rw [← Finset.sum_mul,hp1,one_mul] at hs
  linarith

end DRGPR.ObliviousFactorization
#print axioms DRGPR.ObliviousFactorization.zip_project
#print axioms DRGPR.ObliviousFactorization.project_zip
#print axioms DRGPR.ObliviousFactorization.sum_zip
#print axioms DRGPR.ObliviousFactorization.player_normalized
#print axioms DRGPR.ObliviousFactorization.factorization
#print axioms DRGPR.ObliviousFactorization.expectation_factorization
#print axioms DRGPR.ObliviousFactorization.fixed_instance_from_average
