import SwitchConcatenation

noncomputable section
open scoped BigOperators
namespace DRGPR.BlockFlattening
open SupportedInformation HistoryAppend PrimitiveRun PrimitiveConcatenation
variable {E : Type}

def length (b : ℕ) : ℕ → ℕ
  | 0 => 0
  | r+1 => length b r+b

theorem length_eq (b : ℕ) : ∀ r, length b r=b*r := by
  intro r
  induction r with
  | zero => simp [length]
  | succ r ih => simp [length,ih,Nat.mul_succ]

theorem length_boundary (b r : ℕ) : length b r%b=0 := by simp [length_eq]

def flatten (b : ℕ) : (r : ℕ) → Hist (Hist E b) r → Hist E (length b r)
  | 0, _ => ()
  | r+1, h => append (length b r) (flatten b r h.1) b h.2

def unflatten (b : ℕ) : (r : ℕ) → Hist E (length b r) → Hist (Hist E b) r
  | 0, _ => ()
  | r+1, h => (unflatten b r (take (length b r) b h),drop (length b r) b h)

theorem unflatten_flatten (b : ℕ) : ∀ r (h : Hist (Hist E b) r),
    unflatten b r (flatten b r h)=h := by
  intro r
  induction r with
  | zero => intro h; cases h; rfl
  | succ r ih =>
    intro h
    change (unflatten b r (take (length b r) b (append (length b r) (flatten b r h.1) b h.2)),
      drop (length b r) b (append (length b r) (flatten b r h.1) b h.2))=h
    rw [take_append,drop_append,ih]
    rfl

theorem flatten_unflatten (b : ℕ) : ∀ r (h : Hist E (length b r)),
    flatten b r (unflatten b r h)=h := by
  intro r
  induction r with
  | zero => intro h; cases h; rfl
  | succ r ih =>
    intro h
    change append (length b r) (flatten b r (unflatten b r (take (length b r) b h))) b
      (drop (length b r) b h)=h
    rw [ih,append_split]

def equiv (b r : ℕ) : Hist (Hist E b) r ≃ Hist E (length b r) where
  toFun := flatten b r
  invFun := unflatten b r
  left_inv := unflatten_flatten b r
  right_inv := flatten_unflatten b r

theorem sum_flatten [Fintype E] (b r : ℕ) (f : Hist E (length b r) → ℝ) :
    (∑ h, f (flatten b r h))=∑ h, f h :=
  Fintype.sum_equiv (equiv b r) _ _ (fun _ => rfl)

variable {I : Type} [Fintype I] [DecidableEq I]

def blockState (q η : ℝ) (b : ℕ) (p : FiniteController.Dist I) (f : I) :
    (r : ℕ) → Hist (Hist (I → Bool) b) r → Hist (Hist (I × Bool) b) r → State I
  | 0, _, _ => initialState p f
  | r+1, e, a =>
    let previous := blockState q η b p f r e.1 a.1
    state q η b previous.distribution previous.last b (visiblePrefix b e.2 a.2)

theorem state_flatten (q η : ℝ) (b : ℕ) (p : FiniteController.Dist I) (f : I) :
    ∀ r (e : Hist (Hist (I → Bool) b) r) (a : Hist (Hist (I × Bool) b) r),
    state q η b p f (length b r) (visiblePrefix (length b r) (flatten b r e) (flatten b r a))=
      blockState q η b p f r e a := by
  intro r
  induction r with
  | zero => intro e a; rfl
  | succ r ih =>
    intro e a
    change state q η b p f (length b r+b)
      (visiblePrefix (length b r+b) (append (length b r) (flatten b r e.1) b e.2)
        (append (length b r) (flatten b r a.1) b a.2))=_
    rw [visible_append,state_append q η b p f (length b r) _ (length_boundary b r),ih]
    rfl

def blockWeight (q η : ℝ) (b : ℕ) (p : FiniteController.Dist I) (f : I) :
    (r : ℕ) → Hist (Hist (I → Bool) b) r → Hist (Hist (I × Bool) b) r → ℝ
  | 0, _, _ => 1
  | r+1, e, a =>
    let previous := blockState q η b p f r e.1 a.1
    blockWeight q η b p f r e.1 a.1 * ObliviousFactorization.playerWeight
      (ObliviousInformation.choice (algorithm q η b previous.distribution previous.last).p q) b e.2 a.2

/-- The sequential block program and the primitive-history algorithm have
exactly the same likelihood, with every intermediate observation retained. -/
theorem weight_flatten (q η : ℝ) (b : ℕ) (p : FiniteController.Dist I) (f : I) :
    ∀ r (e : Hist (Hist (I → Bool) b) r) (a : Hist (Hist (I × Bool) b) r),
    ObliviousFactorization.playerWeight (ObliviousInformation.choice (algorithm q η b p f).p q)
      (length b r) (flatten b r e) (flatten b r a)=blockWeight q η b p f r e a := by
  intro r
  induction r with
  | zero => intro e a; rfl
  | succ r ih =>
    intro e a
    change ObliviousFactorization.playerWeight _ (length b r+b)
      (append (length b r) (flatten b r e.1) b e.2)
      (append (length b r) (flatten b r a.1) b a.2)=_
    rw [player_weight_append q η b p f (length b r) _ _ (length_boundary b r),ih,state_flatten]
    rfl

theorem trajectory_expectation (q η : ℝ) (b r : ℕ) (p : FiniteController.Dist I) (f : I)
    (e : Hist (Hist (I → Bool) b) r) (g : Hist (I × Bool) (length b r) → ℝ) :
    (∑ a, ObliviousFactorization.playerWeight (ObliviousInformation.choice (algorithm q η b p f).p q)
      (length b r) (flatten b r e) a*g a)=
      ∑ a, blockWeight q η b p f r e a*g (flatten b r a) := by
  have he := sum_flatten b r (fun a =>
    ObliviousFactorization.playerWeight (ObliviousInformation.choice (algorithm q η b p f).p q)
      (length b r) (flatten b r e) a*g a)
  simp_rw [weight_flatten] at he
  exact he.symm

end DRGPR.BlockFlattening
#print axioms DRGPR.BlockFlattening.length_eq
#print axioms DRGPR.BlockFlattening.length_boundary
#print axioms DRGPR.BlockFlattening.unflatten_flatten
#print axioms DRGPR.BlockFlattening.flatten_unflatten
#print axioms DRGPR.BlockFlattening.sum_flatten
#print axioms DRGPR.BlockFlattening.state_flatten
#print axioms DRGPR.BlockFlattening.weight_flatten
#print axioms DRGPR.BlockFlattening.trajectory_expectation
