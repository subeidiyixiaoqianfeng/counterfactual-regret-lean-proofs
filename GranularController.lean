import GranularObservation
import LocalVariance
import ControllerInterfaces

noncomputable section
open scoped BigOperators
namespace DRGPR.GranularController
open FiniteController TableDistribution GranularObservation SupportedInformation
variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

/-- The run feedback is built from independent primitive-round masks.
The feedback score bound is card(J)/q, not the task duration. -/
def feedback (q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1)
    (l : I → J → ℝ) (hl : ∀ i t, 0 ≤ l i t) (hl1 : ∀ i t, l i t ≤ 1) :
    Feedback I (J → Bool) where
  kernel _ := row (fun _ => q)
  kernel_nonneg _ := row_nonneg _ (fun _ => hq.le) (fun _ => hq1)
  kernel_sum _ := row_normalized _
  accepted _ _ := true
  score i := score q (l i)
  d := (Fintype.card J:ℝ)/q
  d_nonneg := by positivity
  score_nonneg i := GranularObservation.score_nonneg q hq.le (l i) (hl i)
  score_le i := score_bounded q hq (l i) (hl i) (hl1 i)
  q _ := 1
  q_pos _ := by norm_num
  q_def _ := by simpa using row_normalized (fun _ : J => q)
  loss i := ∑ t, l i t
  moment i := by simpa using score_mean q hq.ne' (l i)

theorem exact_second (q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1)
    (l : I → J → ℝ) (hl : ∀ i t, 0 ≤ l i t) (hl1 : ∀ i t, l i t ≤ 1)
    (p : FiniteController.Dist I) (hp : ∀ i, 0 < p.val i) :
    let D := (feedback q hq hq1 l hl hl1).round p
    D.avg (fun draw o => ∑ i, p.val i*(D.estimate draw o i)^2) =
      ∑ i, ∑ x, row (fun _ : J => q) x*(score q (l i) x)^2 := by
  dsimp only
  let D := (feedback q hq hq1 l hl hl1).round p
  change D.avg (fun draw o => ∑ i, p.val i*(D.estimate draw o i)^2) = _
  rw [RandomObservation.Round.avg_sum]
  simp_rw [RandomObservation.Round.avg_const_mul]
  apply Finset.sum_congr rfl
  intro i _
  have he : D.avg (fun draw o => (D.estimate draw o i)^2) =
      p.val i*((∑ x, row (fun _ : J => q) x*(score q (l i) x)^2)/(p.val i)^2) := by
    simp [D,Feedback.round,feedback,RandomObservation.Round.avg,
      RandomObservation.Round.estimate,RandomObservation.Round.usedScore,
      div_pow,← mul_div_assoc,← Finset.sum_div]
  rw [he]
  field_simp [(hp i).ne']
  ring

theorem weighted_second (q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1)
    (l : I → J → ℝ) (hl : ∀ i t, 0 ≤ l i t) (hl1 : ∀ i t, l i t ≤ 1)
    (p : FiniteController.Dist I) (hp : ∀ i, 0 < p.val i) :
    let D := (feedback q hq hq1 l hl hl1).round p
    D.avg (fun draw o => ∑ i, p.val i*(D.estimate draw o i)^2) ≤
      (Fintype.card I:ℝ)*((Fintype.card J:ℝ)^2+(Fintype.card J:ℝ)/q) := by
  dsimp only
  rw [exact_second q hq hq1 l hl hl1 p hp]
  calc
    _ ≤ ∑ _i : I, ((Fintype.card J:ℝ)^2+(Fintype.card J:ℝ)/q) :=
      Finset.sum_le_sum (fun i _ => score_second_bound q hq hq1 (l i) (hl i) (hl1 i))
    _ = _ := by simp; ring

def algorithm (q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1) (η : ℝ) (hη : 0 < η)
    (initial : FiniteController.Dist I)
    (l : (n : ℕ) → Hist (I × (J → Bool)) n → I → J → ℝ)
    (hl : ∀ n h i t, 0 ≤ l n h i t) (hl1 : ∀ n h i t, l n h i t ≤ 1) :
    Program I (J → Bool) where
  initial := initial
  feedback n h := feedback q hq hq1 (l n h) (hl n h) (hl1 n h)
  transition _ _ := identityRows
  η := η
  rate_pos := hη

theorem algorithm_regret (q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1) (η : ℝ) (hη : 0 < η)
    (initial : FiniteController.Dist I) (hi : ∀ i, 0 < initial.val i)
    (l : (n : ℕ) → Hist (I × (J → Bool)) n → I → J → ℝ)
    (hl : ∀ n h i t, 0 ≤ l n h i t) (hl1 : ∀ n h i t, l n h i t ≤ 1)
    (N : ℕ) (j : I) :
    let A := algorithm q hq hq1 η hη initial l hl hl1
    (∑ h, pathLaw A.kernel N h*cumulative (A.actualGap (fun _ _ => j)) N h) ≤
      -Real.log (initial.val j)/η+η/2*((N:ℝ)*(Fintype.card I:ℝ)*
        ((Fintype.card J:ℝ)^2+(Fintype.card J:ℝ)/q)) := by
  let A := algorithm q hq hq1 η hη initial l hl hl1
  have htrans (i : I) : ∀ n (h : Hist (I × (J → Bool)) (n+1)),
      0 < (A.transition n h i).val i := by
    intro n h
    simp [A,algorithm,identityRows]
  have hactive (n : ℕ) (h : Hist (I × (J → Bool)) n) (i : I) :
      0 < (A.state n h).val i := A.bridge_active (fun _ _ => i) (hi i) (htrans i) n h
  have hzero : ∀ n h, cumulative (A.codeIncrement (fun _ _ => j)) n h = 0 := by
    intro n
    induction n with
    | zero => intro h; rfl
    | succ n ih =>
      intro h
      rw [cumulative,ih]
      simp [Program.codeIncrement,A,algorithm,identityRows]
  have hcode : ∀ h, -Real.log (A.initial.val j)+
      cumulative (A.codeIncrement (fun _ _ => j)) N h ≤ -Real.log (initial.val j) := by
    intro h
    rw [hzero]
    simp [A,algorithm]
  let V := (Fintype.card I:ℝ)*((Fintype.card J:ℝ)^2+(Fintype.card J:ℝ)/q)
  have hv (n : ℕ) (h : Hist (I × (J → Bool)) n) :
      (A.round n h).avg (fun i o =>
        DRGPR.mean (A.state n h).val (fun k => ((A.round n h).estimate i o k)^2)) ≤ V :=
    weighted_second q hq hq1 (l n h) (hl n h) (hl1 n h) (A.state n h) (hactive n h)
  have h := A.regret_local_variance (fun _ _ => j) N (-Real.log (initial.val j))
    (hi j) (htrans j) hcode (fun _ _ => V) hv
  have hvsum : (∑ n ∈ Finset.range N, ∑ h, pathLaw A.kernel n h*V)=(N:ℝ)*V := by
    simp [← Finset.sum_mul,A.law_normalized]
  rw [hvsum] at h
  dsimp [A,algorithm] at h ⊢
  convert h using 1 <;> dsimp [V] <;> ring

end DRGPR.GranularController
#print axioms DRGPR.GranularController.exact_second
#print axioms DRGPR.GranularController.weighted_second
#print axioms DRGPR.GranularController.algorithm_regret
