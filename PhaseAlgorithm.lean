import HistoryLookup
import PhaseTuning

noncomputable section
open scoped BigOperators
namespace DRGPR.PhaseAlgorithm
open FiniteController SupportedInformation PhaseSchedule HistoryLookup
variable {I : Type} [Fintype I] [DecidableEq I]

def uniform (hK : (0:ℝ) < Fintype.card I) : FiniteController.Dist I where
  val _ := 1/(Fintype.card I:ℝ)
  nonneg _ := by positivity
  sum_one := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; field_simp

theorem uniform_pos (hK : (0:ℝ) < Fintype.card I) (i : I) : 0 < (uniform hK).val i := by
  dsimp [uniform]
  positivity

theorem uniform_code (hK : (0:ℝ) < Fintype.card I) (i : I) :
    -Real.log ((uniform hK).val i)=Real.log (Fintype.card I) := by
  simp [uniform,Real.log_div]

def algorithm (T b : ℕ) (q η : ℝ) (hq : 0 < q) (hq1 : q ≤ 1) (hη : 0 < η)
    (hK : (0:ℝ) < Fintype.card I) (l : I → Fin T → ℝ)
    (hl : ∀ i t, 0 ≤ l i t) (hl1 : ∀ i t, l i t ≤ 1) : Program I (Fin T → Bool) :=
  VariableRunController.algorithm q hq hq1 η hη (uniform hK)
    (fun r _ => slots T b r) (fun _ _ => l) (fun _ _ => hl) (fun _ _ => hl1)

def learnerTotal (T b : ℕ) (l : I → Fin T → ℝ) (h : Hist (I × (Fin T → Bool)) T) : ℝ :=
  ∑ t, l (lookup T h (runOf T b t)).1 t

def comparatorTotal (T : ℕ) (l : I → Fin T → ℝ) (j : I) : ℝ := ∑ t, l j t

theorem actual_gap_identity (T b : ℕ) (q η : ℝ) (hq : 0 < q) (hq1 : q ≤ 1) (hη : 0 < η)
    (hK : (0:ℝ) < Fintype.card I) (l : I → Fin T → ℝ)
    (hl : ∀ i t, 0 ≤ l i t) (hl1 : ∀ i t, l i t ≤ 1)
    (j : I) (h : Hist (I × (Fin T → Bool)) T) :
    let A := algorithm T b q η hq hq1 hη hK l hl hl1
    cumulative (A.actualGap (fun _ _ => j)) T h=learnerTotal T b l h-comparatorTotal T l j := by
  dsimp only
  have he : (algorithm T b q η hq hq1 hη hK l hl hl1).actualGap (fun _ _ => j)=
      (fun r _ a => (∑ t ∈ slots T b r, l a.1 t)-(∑ t ∈ slots T b r, l j t)) := by
    funext r hist a
    simp [Program.actualGap,algorithm,VariableRunController.algorithm,
      GranularController.algorithm,GranularController.feedback,VariableRunController.masked_sum]
  rw [he,cumulative_lookup]
  rw [Finset.sum_sub_distrib,regroup_runs,constant_regroup]
  rfl

/-- The primitive task loss is derived from executed run identities, not supplied as an assumed gap. -/
theorem expected_base_regret (T b : ℕ) (hb : 0 < b) (q η : ℝ)
    (hq : 0 < q) (hq1 : q ≤ 1) (hη : 0 < η)
    (hK : (0:ℝ) < Fintype.card I) (l : I → Fin T → ℝ)
    (hl : ∀ i t, 0 ≤ l i t) (hl1 : ∀ i t, l i t ≤ 1) (j : I) :
    let A := algorithm T b q η hq hq1 hη hK l hl hl1
    (∑ h, pathLaw A.kernel T h*learnerTotal T b l h)-comparatorTotal T l j ≤
      Real.log (Fintype.card I)/η+η/2*((Fintype.card I:ℝ)*((b:ℝ)+1/q)*T) := by
  let A := algorithm T b q η hq hq1 hη hK l hl hl1
  have hr := VariableRunController.variable_run_regret q hq hq1 η hη (uniform hK)
    (uniform_pos hK) (fun r _ => slots T b r) (fun _ _ => l) (fun _ _ => hl) (fun _ _ => hl1)
    T j b T (Nat.cast_nonneg _) (fun r _ => by exact_mod_cast slots_card_le T b r hb)
    (fun h => (path_duration_exact T b h).le)
  change (∑ h, pathLaw A.kernel T h*cumulative (A.actualGap (fun _ _ => j)) T h) ≤ _ at hr
  have hg : ∀ h, cumulative (A.actualGap (fun _ _ => j)) T h=
      learnerTotal T b l h-comparatorTotal T l j := actual_gap_identity T b q η hq hq1 hη hK l hl hl1 j
  simp_rw [hg] at hr
  rw [uniform_code] at hr
  change DRGPR.mean (pathLaw A.kernel T) (fun h => learnerTotal T b l h-comparatorTotal T l j) ≤ _ at hr
  rw [DRGPR.mean_sub,DRGPR.mean_const _ (A.law_normalized T)] at hr
  exact hr

end DRGPR.PhaseAlgorithm
#print axioms DRGPR.PhaseAlgorithm.uniform_pos
#print axioms DRGPR.PhaseAlgorithm.uniform_code
#print axioms DRGPR.PhaseAlgorithm.actual_gap_identity
#print axioms DRGPR.PhaseAlgorithm.expected_base_regret
