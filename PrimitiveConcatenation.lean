import HistoryAppend

noncomputable section
open scoped BigOperators
namespace DRGPR.PrimitiveConcatenation
open SupportedInformation PrimitiveRun HistoryAppend
variable {I : Type} [Fintype I] [DecidableEq I]

theorem advance_shift (q η : ℝ) (b n t : ℕ) (hn : n%b=0)
    (s : State I) (a : I × Option Bool) : advance q η b (n+t) s a=advance q η b t s a := by
  have hm : (n+t+1)%b=(t+1)%b := by rw [Nat.add_assoc,Nat.add_mod,hn]; simp
  simp only [advance,hm]

theorem state_zero_accumulator (q η : ℝ) (b : ℕ) (p : FiniteController.Dist I) (f : I)
    (n : ℕ) (h : Hist (I × Option Bool) n) (hn : n%b=0) :
    (state q η b p f n h).accumulated=0 := by
  cases n with
  | zero => rfl
  | succ n => simp [state,advance,hn]

theorem initial_of_zero (s : State I) (hz : s.accumulated=0) :
    s=initialState s.distribution s.last := by
  cases s
  simp only at hz
  subst hz
  rfl

/-- Restarting a run interpreter at a public multiple of its cap preserves
the actual state. Only the already received prefix determines that state. -/
theorem state_append (q η : ℝ) (b : ℕ) (p : FiniteController.Dist I) (f : I)
    (n : ℕ) (h : Hist (I × Option Bool) n) (hn : n%b=0) :
    ∀ m (g : Hist (I × Option Bool) m),
    state q η b p f (n+m) (append n h m g)=
      state q η b (state q η b p f n h).distribution (state q η b p f n h).last m g := by
  intro m
  induction m with
  | zero => intro g; exact initial_of_zero _ (state_zero_accumulator q η b p f n h hn)
  | succ m ih =>
    intro g
    change advance q η b (n+m) (state q η b p f (n+m) (append n h m g.1)) g.2=_
    rw [ih,advance_shift q η b n m hn]
    rfl

theorem distribution_append (q η : ℝ) (b : ℕ) (p : FiniteController.Dist I) (f : I)
    (n : ℕ) (h : Hist (I × Option Bool) n) (hn : n%b=0)
    (m : ℕ) (g : Hist (I × Option Bool) m) :
    distribution q η b p f (n+m) (append n h m g)=
      distribution q η b (state q η b p f n h).distribution (state q η b p f n h).last m g := by
  have hm : (n+m)%b=m%b := by rw [Nat.add_mod,hn]; simp
  simp only [distribution,hm,state_append q η b p f n h hn]

def visiblePrefix (n : ℕ) (e : Hist (I → Bool) n) (a : Hist (I × Bool) n) :=
  FiniteSimulation.project ObliviousInformation.visible n (ObliviousFactorization.zip n e a)

theorem visible_append (n : ℕ) (e : Hist (I → Bool) n) (a : Hist (I × Bool) n)
    (m : ℕ) (g : Hist (I → Bool) m) (c : Hist (I × Bool) m) :
    visiblePrefix (n+m) (append n e m g) (append n a m c)=
      append n (visiblePrefix n e a) m (visiblePrefix m g c) := by
  unfold visiblePrefix
  rw [zip_append,project_append]

theorem choice_append (q η : ℝ) (b : ℕ) (p : FiniteController.Dist I) (f : I)
    (n : ℕ) (e : Hist (I → Bool) n) (a : Hist (I × Bool) n) (hn : n%b=0)
    (m : ℕ) (g : Hist (I → Bool) m) (c : Hist (I × Bool) m) (z : I × Bool) :
    ObliviousInformation.choice (algorithm q η b p f).p q
      (n+m) (append n e m g) (append n a m c) z =
    ObliviousInformation.choice (algorithm q η b
      (state q η b p f n (visiblePrefix n e a)).distribution
      (state q η b p f n (visiblePrefix n e a)).last).p q m g c z := by
  change (distribution q η b p f (n+m)
    (visiblePrefix (n+m) (append n e m g) (append n a m c))).val z.1 * _ = _
  rw [visible_append,distribution_append q η b p f n (visiblePrefix n e a) hn]
  rfl

/-- This factorization retains the complete emitted primitive observations.
It does not assume a path likelihood or a simulation identity. -/
theorem player_weight_append (q η : ℝ) (b : ℕ) (p : FiniteController.Dist I) (f : I)
    (n : ℕ) (e : Hist (I → Bool) n) (a : Hist (I × Bool) n) (hn : n%b=0) :
    ∀ m (g : Hist (I → Bool) m) (c : Hist (I × Bool) m),
    ObliviousFactorization.playerWeight (ObliviousInformation.choice (algorithm q η b p f).p q)
      (n+m) (append n e m g) (append n a m c) =
    ObliviousFactorization.playerWeight (ObliviousInformation.choice (algorithm q η b p f).p q) n e a *
    ObliviousFactorization.playerWeight (ObliviousInformation.choice (algorithm q η b
      (state q η b p f n (visiblePrefix n e a)).distribution
      (state q η b p f n (visiblePrefix n e a)).last).p q) m g c := by
  intro m
  induction m with
  | zero => intro g c; simp [append,ObliviousFactorization.playerWeight]
  | succ m ih =>
    intro g c
    change ObliviousFactorization.playerWeight _ (n+m) (append n e m g.1) (append n a m c.1) *
      ObliviousInformation.choice (algorithm q η b p f).p q
        (n+m) (append n e m g.1) (append n a m c.1) c.2 = _
    rw [ih,choice_append q η b p f n e a hn]
    simp only [ObliviousFactorization.playerWeight,mul_assoc]

end DRGPR.PrimitiveConcatenation
#print axioms DRGPR.PrimitiveConcatenation.advance_shift
#print axioms DRGPR.PrimitiveConcatenation.state_zero_accumulator
#print axioms DRGPR.PrimitiveConcatenation.initial_of_zero
#print axioms DRGPR.PrimitiveConcatenation.state_append
#print axioms DRGPR.PrimitiveConcatenation.distribution_append
#print axioms DRGPR.PrimitiveConcatenation.visible_append
#print axioms DRGPR.PrimitiveConcatenation.choice_append
#print axioms DRGPR.PrimitiveConcatenation.player_weight_append
