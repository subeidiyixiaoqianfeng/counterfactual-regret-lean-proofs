import ScheduledObservable
import GrowingTaskLower

noncomputable section
open scoped BigOperators
namespace DRGPR.PrimitiveRun
open SupportedInformation FiniteController
variable {I : Type} [Fintype I] [DecidableEq I]

/-- A score computed from a received primitive observation only. -/
def receivedScore (q : ℝ) : Option Bool → ℝ
  | none => 0
  | some y => ObliviousInformation.loss y/q

structure State (I : Type) [Fintype I] where
  distribution : FiniteController.Dist I
  last : I
  accumulated : ℝ

def initialState (p : FiniteController.Dist I) (fallback : I) : State I := ⟨p,fallback,0⟩

/-- At a segment end, apply exactly one update to its accumulated score.
This function has no hidden table argument. -/
def advance (q η : ℝ) (b t : ℕ) (s : State I) (a : I × Option Bool) : State I :=
  let z := s.accumulated+receivedScore q a.2
  if (t+1)%b=0 then
    ⟨update s.distribution (GranularObservable.importance s.distribution (a.1,z)) η identityRows,a.1,0⟩
  else ⟨s.distribution,a.1,z⟩

def state (q η : ℝ) (b : ℕ) (p : FiniteController.Dist I) (fallback : I) :
    (t : ℕ) → Hist (I × Option Bool) t → State I
  | 0, _ => initialState p fallback
  | t+1, h => advance q η b t (state q η b p fallback t h.1) h.2

def distribution (q η : ℝ) (b : ℕ) (p : FiniteController.Dist I) (fallback : I)
    (t : ℕ) (h : Hist (I × Option Bool) t) : FiniteController.Dist I :=
  if t%b=0 then (state q η b p fallback t h).distribution
  else identityRows (state q η b p fallback t h).last

/-- This is an inhabitant of the primitive-transcript algorithm type used
in the lower bound, without providing a loss table to the constructor. -/
def algorithm (q η : ℝ) (b : ℕ) (p : FiniteController.Dist I) (fallback : I) : ObliviousMinimax.Algorithm I where
  p t h := (distribution q η b p fallback t h).val
  nonneg t h := (distribution q η b p fallback t h).nonneg
  normalized t h := (distribution q η b p fallback t h).sum_one

theorem at_start (q η : ℝ) (b : ℕ) (p : FiniteController.Dist I) (fallback : I)
    (t : ℕ) (h : Hist (I × Option Bool) t) (ht : t%b=0) :
    (algorithm q η b p fallback).p t h=(state q η b p fallback t h).distribution.val := by
  simp [algorithm,distribution,ht]

theorem inside_run (q η : ℝ) (b : ℕ) (p : FiniteController.Dist I) (fallback : I)
    (t : ℕ) (h : Hist (I × Option Bool) t) (ht : t%b≠0) (i : I) :
    (algorithm q η b p fallback).p t h i=
      if (state q η b p fallback t h).last=i then 1 else 0 := by
  simp [algorithm,distribution,ht,identityRows]

theorem last_is_executed (q η : ℝ) (b t : ℕ) (p : FiniteController.Dist I) (fallback : I)
    (h : Hist (I × Option Bool) (t+1)) :
    (state q η b p fallback (t+1) h).last=h.2.1 := by
  simp [state,advance]
  split_ifs <;> rfl

theorem no_update_inside (q η : ℝ) (b t : ℕ) (s : State I) (a : I × Option Bool)
    (ht : (t+1)%b≠0) :
    (advance q η b t s a).distribution=s.distribution ∧
    (advance q η b t s a).accumulated=s.accumulated+receivedScore q a.2 := by
  simp [advance,ht]

theorem update_at_end (q η : ℝ) (b t : ℕ) (s : State I) (a : I × Option Bool)
    (ht : (t+1)%b=0) :
    (advance q η b t s a).distribution=
      update s.distribution (GranularObservable.importance s.distribution
        (a.1,s.accumulated+receivedScore q a.2)) η identityRows ∧
    (advance q η b t s a).accumulated=0 := by
  simp [advance,ht]

def scoreTotal (q : ℝ) := @cumulative (Option Bool) (fun _ _ o => receivedScore q o)

/-- Run the actual update interpreter on a transcript holding one identity. -/
def heldState (q η : ℝ) (b : ℕ) (p : FiniteController.Dist I) (i : I) :
    (t : ℕ) → Hist (Option Bool) t → State I
  | 0, _ => initialState p i
  | t+1, h => advance q η b t (heldState q η b p i t h.1) (i,h.2)

theorem held_state_is_actual (q η : ℝ) (b : ℕ) (p : FiniteController.Dist I) (i : I) :
    ∀ t (h : Hist (Option Bool) t),
    state q η b p i t (FiniteSimulation.project (fun o => (i,o)) t h)=heldState q η b p i t h := by
  intro t
  induction t with
  | zero => intro h; rfl
  | succ t ih =>
    intro h
    change advance q η b t (state q η b p i t (FiniteSimulation.project (fun o => (i,o)) t h.1)) (i,h.2)=advance q η b t (heldState q η b p i t h.1) (i,h.2)
    rw [ih]

theorem held_before_end (q η : ℝ) (b : ℕ) (p : FiniteController.Dist I) (i : I) :
    ∀ t (h : Hist (Option Bool) t), t < b →
      (heldState q η b p i t h).distribution=p ∧
      (heldState q η b p i t h).last=i ∧
      (heldState q η b p i t h).accumulated=scoreTotal q t h := by
  intro t
  induction t with
  | zero => intro h ht; simp [heldState,initialState,scoreTotal,cumulative]
  | succ t ih =>
    intro h ht
    have hp := ih h.1 (by omega)
    have hz : (t+1)%b≠0 := by rw [Nat.mod_eq_of_lt ht]; omega
    change (advance q η b t (heldState q η b p i t h.1) (i,h.2)).distribution=p ∧
      (advance q η b t (heldState q η b p i t h.1) (i,h.2)).last=i ∧
      (advance q η b t (heldState q η b p i t h.1) (i,h.2)).accumulated=scoreTotal q (t+1) h
    simp only [advance,hz,ite_false,hp.1,hp.2.2]
    simp [scoreTotal,cumulative]

/-- At a full segment boundary, the primitive interpreter performs exactly
the macro update with the received segment score, not a fresh guessed loss. -/
theorem full_run_update (q η : ℝ) (d : ℕ) (p : FiniteController.Dist I) (i : I)
    (h : Hist (Option Bool) (d+1)) :
    (heldState q η (d+1) p i (d+1) h).distribution=
      update p (GranularObservable.importance p (i,scoreTotal q (d+1) h)) η identityRows ∧
    (heldState q η (d+1) p i (d+1) h).accumulated=0 := by
  have hp := held_before_end q η (d+1) p i d h.1 (by omega)
  have he := update_at_end q η (d+1) d (heldState q η (d+1) p i d h.1) (i,h.2) (by simp)
  rw [hp.1,hp.2.2] at he
  exact he

end DRGPR.PrimitiveRun
#print axioms DRGPR.PrimitiveRun.at_start
#print axioms DRGPR.PrimitiveRun.inside_run
#print axioms DRGPR.PrimitiveRun.last_is_executed
#print axioms DRGPR.PrimitiveRun.no_update_inside
#print axioms DRGPR.PrimitiveRun.update_at_end
#print axioms DRGPR.PrimitiveRun.held_state_is_actual
#print axioms DRGPR.PrimitiveRun.held_before_end
#print axioms DRGPR.PrimitiveRun.full_run_update
