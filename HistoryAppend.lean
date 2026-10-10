import HistoryFunction

noncomputable section
open scoped BigOperators
namespace DRGPR.HistoryAppend
open SupportedInformation
variable {E : Type}

def append (n : ℕ) (h : Hist E n) : (m : ℕ) → Hist E m → Hist E (n+m)
  | 0, _ => h
  | m+1, g => (append n h m g.1,g.2)

def take (n : ℕ) : (m : ℕ) → Hist E (n+m) → Hist E n
  | 0, h => h
  | m+1, h => take n m h.1

def drop (n : ℕ) : (m : ℕ) → Hist E (n+m) → Hist E m
  | 0, _ => ()
  | m+1, h => (drop n m h.1,h.2)

theorem take_append (n : ℕ) (h : Hist E n) : ∀ m (g : Hist E m),
    take n m (append n h m g)=h := by
  intro m
  induction m with
  | zero => intro g; rfl
  | succ m ih => intro g; exact ih g.1

theorem drop_append (n : ℕ) (h : Hist E n) : ∀ m (g : Hist E m),
    drop n m (append n h m g)=g := by
  intro m
  induction m with
  | zero => intro g; cases g; rfl
  | succ m ih => intro g; change (drop n m (append n h m g.1),g.2)=g; rw [ih]; rfl

theorem append_split (n : ℕ) : ∀ m (h : Hist E (n+m)),
    append n (take n m h) m (drop n m h)=h := by
  intro m
  induction m with
  | zero => intro h; rfl
  | succ m ih => intro h; change (append n (take n m h.1) m (drop n m h.1),h.2)=h; rw [ih]; rfl

def splitEquiv (n m : ℕ) : Hist E (n+m) ≃ Hist E n × Hist E m where
  toFun h := (take n m h,drop n m h)
  invFun h := append n h.1 m h.2
  left_inv := append_split n m
  right_inv h := Prod.ext (take_append n h.1 m h.2) (drop_append n h.1 m h.2)

theorem sum_append [Fintype E] (n m : ℕ) (f : Hist E (n+m) → ℝ) :
    (∑ h, f h)=∑ h, ∑ g, f (append n h m g) := by
  have he := Fintype.sum_equiv (splitEquiv n m) f
    (fun z => f (append n z.1 m z.2)) (fun h => by simp [splitEquiv,append_split])
  rw [he,Fintype.sum_prod_type]

def suffixWeight (k : (t : ℕ) → Hist E t → E → ℝ) (n : ℕ) (h : Hist E n) :
    (m : ℕ) → Hist E m → ℝ
  | 0, _ => 1
  | m+1, g => suffixWeight k n h m g.1 * k (n+m) (append n h m g.1) g.2

theorem path_factorization (k : (t : ℕ) → Hist E t → E → ℝ) (n : ℕ) (h : Hist E n) :
    ∀ m (g : Hist E m), pathLaw k (n+m) (append n h m g)=pathLaw k n h*suffixWeight k n h m g := by
  intro m
  induction m with
  | zero => intro g; simp [append,suffixWeight]
  | succ m ih =>
    intro g
    change pathLaw k (n+m) (append n h m g.1)*k (n+m) (append n h m g.1) g.2=_
    rw [ih]
    simp only [suffixWeight,mul_assoc]

theorem project_append {F : Type} (f : E → F) (n : ℕ) (h : Hist E n) :
    ∀ m (g : Hist E m),
    FiniteSimulation.project f (n+m) (append n h m g)=
      append n (FiniteSimulation.project f n h) m (FiniteSimulation.project f m g) := by
  intro m
  induction m with
  | zero => intro g; rfl
  | succ m ih =>
    intro g
    change (FiniteSimulation.project f (n+m) (append n h m g.1),f g.2)=_
    rw [ih]
    rfl

theorem zip_append {F : Type} (n : ℕ) (h : Hist E n) (k : Hist F n) :
    ∀ m (g : Hist E m) (l : Hist F m),
    ObliviousFactorization.zip (n+m) (append n h m g) (append n k m l)=
      append n (ObliviousFactorization.zip n h k) m (ObliviousFactorization.zip m g l) := by
  intro m
  induction m with
  | zero => intro g l; rfl
  | succ m ih =>
    intro g l
    change (ObliviousFactorization.zip (n+m) (append n h m g.1) (append n k m l.1),(g.2,l.2))=_
    rw [ih]
    rfl

end DRGPR.HistoryAppend
#print axioms DRGPR.HistoryAppend.take_append
#print axioms DRGPR.HistoryAppend.drop_append
#print axioms DRGPR.HistoryAppend.append_split
#print axioms DRGPR.HistoryAppend.sum_append
#print axioms DRGPR.HistoryAppend.path_factorization
#print axioms DRGPR.HistoryAppend.project_append
#print axioms DRGPR.HistoryAppend.zip_append
