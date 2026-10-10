import PrimitiveRun

noncomputable section
open scoped BigOperators
namespace DRGPR.HistoryFunction
open SupportedInformation HistoryLookup
variable {E : Type}

def ofFn : (n : ℕ) → (Fin n → E) → Hist E n
  | 0, _ => ()
  | n+1, f => (ofFn n (fun i => f i.castSucc),f (Fin.last n))

theorem lookup_ofFn : ∀ n (f : Fin n → E) (i : Fin n), lookup n (ofFn n f) i=f i := by
  intro n
  induction n with
  | zero => intro f i; exact Fin.elim0 i
  | succ n ih =>
    intro f i
    by_cases hi : i.val < n
    · have he : (⟨i.val,hi⟩ : Fin n).castSucc=i := Fin.ext rfl
      simp only [ofFn,lookup,dif_pos hi]
      rw [ih,he]
    · have he : i=Fin.last n := Fin.ext (by have := i.isLt; simp only [Fin.val_last]; omega)
      subst i
      simp [ofFn,lookup]

theorem ofFn_lookup : ∀ n (h : Hist E n), ofFn n (lookup n h)=h := by
  intro n
  induction n with
  | zero => intro h; cases h; rfl
  | succ n ih =>
    intro h
    change (ofFn n (fun i => lookup (n+1) h i.castSucc),lookup (n+1) h (Fin.last n))=h
    simp only [lookup_castSucc,lookup_last,ih]
    rfl

def equiv (n : ℕ) : Hist E n ≃ (Fin n → E) where
  toFun := lookup n
  invFun := ofFn n
  left_inv := ofFn_lookup n
  right_inv f := funext (lookup_ofFn n f)

theorem sum_history [Fintype E] (n : ℕ) (f : Hist E n → ℝ) :
    (∑ h, f h)=∑ x : Fin n → E, f (ofFn n x) :=
  Fintype.sum_equiv (equiv n) _ _ (fun h => by simp [equiv,ofFn_lookup])

def productWeight (w : ℕ → E → ℝ) : (n : ℕ) → Hist E n → ℝ
  | 0, _ => 1
  | n+1, h => productWeight w n h.1*w n h.2

theorem productWeight_lookup (w : ℕ → E → ℝ) : ∀ n (h : Hist E n),
    productWeight w n h=∏ t : Fin n, w t.val (lookup n h t) := by
  intro n
  induction n with
  | zero => intro h; simp [productWeight]
  | succ n ih =>
    intro h
    rw [Fin.prod_univ_castSucc]
    simp only [lookup_castSucc,lookup_last,Fin.coe_castSucc,Fin.val_last]
    exact congrArg (fun z => z*w n h.2) (ih h.1)

theorem bernoulli_weight (q : ℝ) (n : ℕ) (h : Hist Bool n) :
    productWeight (fun _ => ErasedBandit.bernoulli q) n h=
      TableDistribution.row (fun _ : Fin n => q) (lookup n h) := by
  rw [productWeight_lookup]
  rfl

theorem bernoulli_expectation (q : ℝ) (n : ℕ) (f : Hist Bool n → ℝ) :
    (∑ h, productWeight (fun _ => ErasedBandit.bernoulli q) n h*f h)=
      ∑ x : Fin n → Bool, TableDistribution.row (fun _ => q) x*f (ofFn n x) := by
  rw [sum_history]
  apply Finset.sum_congr rfl
  intro x _
  rw [bernoulli_weight]
  have he : lookup n (ofFn n x)=x := funext (lookup_ofFn n x)
  rw [he]

end DRGPR.HistoryFunction
#print axioms DRGPR.HistoryFunction.lookup_ofFn
#print axioms DRGPR.HistoryFunction.ofFn_lookup
#print axioms DRGPR.HistoryFunction.sum_history
#print axioms DRGPR.HistoryFunction.productWeight_lookup
#print axioms DRGPR.HistoryFunction.bernoulli_weight
#print axioms DRGPR.HistoryFunction.bernoulli_expectation
