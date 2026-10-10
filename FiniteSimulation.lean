import SupportedInformation
import FiniteStochastic

noncomputable section
open scoped BigOperators
namespace DRGPR.FiniteSimulation
open SupportedInformation

def project {A B : Type} (f : B → A) : (n : ℕ) → Hist B n → Hist A n
  | 0, _ => ()
  | n+1, h => (project f n h.1, f h.2)

instance histDecidableEq {A : Type} [DecidableEq A] : (n : ℕ) → DecidableEq (Hist A n)
  | 0 => inferInstanceAs (DecidableEq Unit)
  | n+1 => by
    letI : DecidableEq (Hist A n) := histDecidableEq n
    exact inferInstanceAs (DecidableEq (Hist A n × A))

theorem projected_path_law {A B : Type} [Fintype A] [Fintype B] [DecidableEq A]
    (f : B → A)
    (k : (n : ℕ) → Hist A n → A → ℝ)
    (l : (n : ℕ) → Hist B n → B → ℝ)
    (hlocal : ∀ n h a, (∑ b, if f b=a then l n h b else 0)=k n (project f n h) a) :
    ∀ n h, (∑ g, if project f n g=h then pathLaw l n g else 0)=pathLaw k n h := by
  intro n
  induction n with
  | zero => intro h; cases h; simp [Hist,project,pathLaw]
  | succ n ih =>
    intro h
    change (∑ g : Hist B n × B, if (project f n g.1,f g.2)=h then
      pathLaw l n g.1*l n g.1 g.2 else 0)=pathLaw k n h.1*k n h.1 h.2
    rw [Fintype.sum_prod_type]
    have he (g : Hist B n) :
        (∑ b, if (project f n g,f b)=h then pathLaw l n g*l n g b else 0)=
          (if project f n g=h.1 then pathLaw l n g else 0)*k n h.1 h.2 := by
      by_cases hg : project f n g=h.1
      · have hx (b : B) : (project f n g,f b)=h ↔ f b=h.2 := by
          cases h
          simp [hg]
        simp only [hx, if_pos hg]
        have hp : (∑ b, if f b=h.2 then pathLaw l n g*l n g b else 0)=
            pathLaw l n g*(∑ b, if f b=h.2 then l n g b else 0) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro b _
          split_ifs <;> ring
        rw [hp,hlocal,hg]
      · have hx (b : B) : (project f n g,f b) ≠ h := by
          intro hh
          exact hg (congrArg Prod.fst hh)
        simp [hg,hx]
    simp_rw [he]
    rw [← Finset.sum_mul,ih]

theorem projected_expectation {A B : Type} [Fintype A] [Fintype B] [DecidableEq A]
    (f : B → A)
    (k : (n : ℕ) → Hist A n → A → ℝ)
    (l : (n : ℕ) → Hist B n → B → ℝ)
    (hlocal : ∀ n h a, (∑ b, if f b=a then l n h b else 0)=k n (project f n h) a)
    (n : ℕ) (g : Hist A n → ℝ) :
    (∑ h, pathLaw l n h*g (project f n h)) = ∑ h, pathLaw k n h*g h := by
  exact FiniteStochastic.pushforward_mean (pathLaw l n) (project f n) (pathLaw k n)
    (projected_path_law f k l hlocal n) g

theorem cumulative_projection {A B : Type} (f : B → A)
    (c : (n : ℕ) → Hist A n → A → ℝ) :
    ∀ n h, cumulative (fun r g b => c r (project f r g) (f b)) n h =
      cumulative c n (project f n h) := by
  intro n
  induction n with
  | zero => intro h; rfl
  | succ n ih => intro h; change _ + _ = _ + _; rw [ih]; rfl

end DRGPR.FiniteSimulation
#print axioms DRGPR.FiniteSimulation.projected_path_law
#print axioms DRGPR.FiniteSimulation.projected_expectation
#print axioms DRGPR.FiniteSimulation.cumulative_projection
