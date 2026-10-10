import PhaseFlattening

noncomputable section
open scoped BigOperators
namespace DRGPR.BlockMacroEncoding
open SupportedInformation PrimitiveRun SingleRunCoupling HistoryFunction BlockFlattening
open FiniteController
variable {I : Type} [Fintype I] [DecidableEq I]

def tables (d : ℕ) (e : ℕ → Hist (I → Bool) (d+1)) :
    (r : ℕ) → Hist (Hist (I → Bool) (d+1)) r
  | 0 => ()
  | r+1 => (tables d e r,e r)

def record (d : ℕ) (a : I × (Fin (d+1) → Bool)) : Hist (I × Bool) (d+1) :=
  coins a.1 (d+1) (ofFn (d+1) a.2)

def encode (d r : ℕ) := FiniteSimulation.project (record (I:=I) d) r

def losses (d : ℕ) (e : ℕ → Hist (I → Bool) (d+1)) (r : ℕ) (i : I) (t : Fin (d+1)) : ℝ :=
  ObliviousInformation.loss (HistoryLookup.lookup (d+1) (e r) t i)

theorem losses_nonneg (d : ℕ) (e : ℕ → Hist (I → Bool) (d+1)) (r : ℕ) (i : I) (t : Fin (d+1)) :
    0 ≤ losses d e r i t := (ObliviousMinimax.loss_bounds _).1

theorem losses_le (d : ℕ) (e : ℕ → Hist (I → Bool) (d+1)) (r : ℕ) (i : I) (t : Fin (d+1)) :
    losses d e r i t ≤ 1 := (ObliviousMinimax.loss_bounds _).2

def macroAlgorithm (d : ℕ) (e : ℕ → Hist (I → Bool) (d+1))
    (q η : ℝ) (hq : 0 < q) (hq1 : q ≤ 1) (hη : 0 < η) (p : FiniteController.Dist I) :
    Program I (Fin (d+1) → Bool) :=
  GranularController.algorithm q hq hq1 η hη p (fun r _ => losses d e r)
    (fun r _ => losses_nonneg d e r) (fun r _ => losses_le d e r)

theorem state_exact (d : ℕ) (e : ℕ → Hist (I → Bool) (d+1))
    (q η : ℝ) (hq : 0 < q) (hq1 : q ≤ 1) (hη : 0 < η) (p : FiniteController.Dist I) (f : I) :
    ∀ r (h : Hist (I × (Fin (d+1) → Bool)) r),
    (blockState q η (d+1) p f r (tables d e r) (encode d r h)).distribution=
      (macroAlgorithm d e q η hq hq1 hη p).state r h := by
  intro r
  induction r with
  | zero => intro h; rfl
  | succ r ih =>
    intro h
    let prev := blockState q η (d+1) p f r (tables d e r) (encode d r h.1)
    change (RunStateCoupling.endState q η d prev.distribution prev.last (e r)
      (coins h.2.1 (d+1) (ofFn (d+1) h.2.2))).distribution=_
    rw [RunStateCoupling.end_state_exact]
    change update prev.distribution
      (GranularObservable.importance prev.distribution
        (h.2.1,GranularObservation.score q (losses d e r h.2.1) h.2.2)) η identityRows = _
    have hp := ih h.1
    change prev.distribution=(macroAlgorithm d e q η hq hq1 hη p).state r h.1 at hp
    rw [hp]
    symm
    exact congrArg (fun z => update ((macroAlgorithm d e q η hq hq1 hη p).state r h.1) z η identityRows)
      (GranularObservable.estimate_from_received q hq hq1 (losses d e r)
        (losses_nonneg d e r) (losses_le d e r)
        ((macroAlgorithm d e q η hq hq1 hη p).state r h.1) h.2)

theorem record_injective (d : ℕ) : Function.Injective (record (I:=I) d) := by
  intro a c h
  have he : (a.1,ofFn (d+1) a.2)=(c.1,ofFn (d+1) c.2) := by
    apply RunDistribution.coins_injective d
    exact h
  have hi := congrArg Prod.fst he
  have hx := congrArg Prod.snd he
  have hf := congrArg (HistoryLookup.lookup (d+1)) hx
  have ha : HistoryLookup.lookup (d+1) (ofFn (d+1) a.2)=a.2 := funext (lookup_ofFn _ _)
  have hc : HistoryLookup.lookup (d+1) (ofFn (d+1) c.2)=c.2 := funext (lookup_ofFn _ _)
  rw [ha,hc] at hf
  exact Prod.ext hi hf

theorem encode_injective (d : ℕ) : ∀ r, Function.Injective (encode (I:=I) d r) := by
  intro r
  induction r with
  | zero => intro a c _; cases a; cases c; rfl
  | succ r ih =>
    intro a c h
    have hp := congrArg Prod.fst h
    have hl := congrArg Prod.snd h
    exact Prod.ext (ih hp) (record_injective d hl)

theorem weight_exact (d : ℕ) (e : ℕ → Hist (I → Bool) (d+1))
    (q η : ℝ) (hq : 0 < q) (hq1 : q ≤ 1) (hη : 0 < η) (p : FiniteController.Dist I) (f : I) :
    ∀ r (h : Hist (I × (Fin (d+1) → Bool)) r),
    blockWeight q η (d+1) p f r (tables d e r) (encode d r h)=
      pathLaw (macroAlgorithm d e q η hq hq1 hη p).kernel r h := by
  intro r
  induction r with
  | zero => intro h; rfl
  | succ r ih =>
    intro h
    let prev := blockState q η (d+1) p f r (tables d e r) (encode d r h.1)
    change blockWeight q η (d+1) p f r (tables d e r) (encode d r h.1) *
      ObliviousFactorization.playerWeight
        (ObliviousInformation.choice (algorithm q η (d+1) prev.distribution prev.last).p q)
        (d+1) (e r) (coins h.2.1 (d+1) (ofFn (d+1) h.2.2))=_
    have hw := held_likelihood q η (d+1) prev.distribution prev.last h.2.1
      (d+1) (e r) (ofFn (d+1) h.2.2) le_rfl
    simp only [Nat.add_eq_zero_iff,Nat.succ_ne_zero,and_false,if_false] at hw
    rw [hw,bernoulli_weight]
    have hx : HistoryLookup.lookup (d+1) (ofFn (d+1) h.2.2)=h.2.2 := funext (lookup_ofFn _ _)
    rw [hx,ih]
    have hp := state_exact d e q η hq hq1 hη p f r h.1
    change prev.distribution=_ at hp
    rw [hp]
    rfl

theorem supported_encoded (d : ℕ) (e : ℕ → Hist (I → Bool) (d+1))
    (q η : ℝ) (p : FiniteController.Dist I) (f : I) :
    ∀ r (a : Hist (Hist (I × Bool) (d+1)) r),
    blockWeight q η (d+1) p f r (tables d e r) a ≠ 0 →
      ∃ h, encode d r h=a := by
  intro r
  induction r with
  | zero => intro a _; cases a; exact ⟨(),rfl⟩
  | succ r ih =>
    intro a hw
    let prev := blockState q η (d+1) p f r (tables d e r) a.1
    change blockWeight q η (d+1) p f r (tables d e r) a.1 *
      ObliviousFactorization.playerWeight
        (ObliviousInformation.choice (algorithm q η (d+1) prev.distribution prev.last).p q)
        (d+1) (e r) a.2 ≠ 0 at hw
    obtain ⟨h,hh⟩ := ih a.1 (mul_ne_zero_iff.mp hw).1
    obtain ⟨i,x,hx⟩ := RunDistribution.supported_is_held q η (d+1) prev.distribution prev.last
      (d+1) (e r) a.2 (by omega) le_rfl (mul_ne_zero_iff.mp hw).2
    refine ⟨(h,(i,HistoryLookup.lookup (d+1) x)),?_⟩
    change (encode d r h,record d (i,HistoryLookup.lookup (d+1) x))=a
    rw [hh]
    simp only [record,ofFn_lookup]
    rw [← hx]
    rfl

/-- Compression is a pushforward of the entire primitive block law. The
proof eliminates unsupported trajectories before identifying macro weights. -/
theorem expectation_exact (d : ℕ) (e : ℕ → Hist (I → Bool) (d+1))
    (q η : ℝ) (hq : 0 < q) (hq1 : q ≤ 1) (hη : 0 < η) (p : FiniteController.Dist I) (f : I)
    (r : ℕ) (g : Hist (Hist (I × Bool) (d+1)) r → ℝ) :
    (∑ a, blockWeight q η (d+1) p f r (tables d e r) a*g a)=
      ∑ h, pathLaw (macroAlgorithm d e q η hq hq1 hη p).kernel r h*g (encode d r h) := by
  have he : (∑ h, blockWeight q η (d+1) p f r (tables d e r) (encode d r h)*g (encode d r h))=
      ∑ a, blockWeight q η (d+1) p f r (tables d e r) a*g a := by
    apply Fintype.sum_of_injective (encode d r) (encode_injective d r)
      (fun h => blockWeight q η (d+1) p f r (tables d e r) (encode d r h)*g (encode d r h))
      (fun a => blockWeight q η (d+1) p f r (tables d e r) a*g a) _ (fun _ => rfl)
    intro a ha
    have hz : blockWeight q η (d+1) p f r (tables d e r) a=0 := by
      by_contra hn
      obtain ⟨h,hh⟩ := supported_encoded d e q η p f r a hn
      exact ha ⟨h,hh⟩
    change blockWeight q η (d+1) p f r (tables d e r) a*g a=0
    rw [hz,zero_mul]
  simp_rw [weight_exact d e q η hq hq1 hη p f] at he
  exact he.symm

theorem primitive_trajectory_law (d : ℕ) (e : ℕ → Hist (I → Bool) (d+1))
    (q η : ℝ) (hq : 0 < q) (hq1 : q ≤ 1) (hη : 0 < η) (p : FiniteController.Dist I) (f : I)
    (r : ℕ) (g : Hist (I × Bool) (length (d+1) r) → ℝ) :
    (∑ a, ObliviousFactorization.playerWeight
      (ObliviousInformation.choice (algorithm q η (d+1) p f).p q) (length (d+1) r)
      (flatten (d+1) r (tables d e r)) a*g a)=
      ∑ h, pathLaw (macroAlgorithm d e q η hq hq1 hη p).kernel r h*
        g (flatten (d+1) r (encode d r h)) := by
  rw [trajectory_expectation]
  exact expectation_exact d e q η hq hq1 hη p f r _

end DRGPR.BlockMacroEncoding
#print axioms DRGPR.BlockMacroEncoding.losses_nonneg
#print axioms DRGPR.BlockMacroEncoding.losses_le
#print axioms DRGPR.BlockMacroEncoding.state_exact
#print axioms DRGPR.BlockMacroEncoding.record_injective
#print axioms DRGPR.BlockMacroEncoding.encode_injective
#print axioms DRGPR.BlockMacroEncoding.weight_exact
#print axioms DRGPR.BlockMacroEncoding.supported_encoded
#print axioms DRGPR.BlockMacroEncoding.expectation_exact
#print axioms DRGPR.BlockMacroEncoding.primitive_trajectory_law
