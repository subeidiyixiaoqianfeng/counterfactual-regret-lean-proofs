import RandomObservation
import SupportedInformation

/- A finite, closed-loop mathematical controller. Its sampling probabilities
are computed recursively from the feedback that it actually receives. No
selection-regret bound or trajectory factorization is a structure field. -/
noncomputable section
open scoped BigOperators
namespace DRGPR.FiniteController
open DRGPR.SupportedInformation

structure Dist (I : Type) [Fintype I] where
  val : I → ℝ
  nonneg : ∀ i, 0 ≤ val i
  sum_one : ∑ i, val i = 1

structure Feedback (I O : Type) [Fintype I] [Fintype O] where
  kernel : I → O → ℝ
  kernel_nonneg : ∀ i o, 0 ≤ kernel i o
  kernel_sum : ∀ i, ∑ o, kernel i o = 1
  accepted : I → O → Bool
  score : I → O → ℝ
  d : ℝ
  d_nonneg : 0 ≤ d
  score_nonneg : ∀ i o, 0 ≤ score i o
  score_le : ∀ i o, score i o ≤ d
  q : I → ℝ
  q_pos : ∀ i, 0 < q i
  q_def : ∀ i, ∑ o, kernel i o * (if accepted i o then 1 else 0) = q i
  loss : I → ℝ
  moment : ∀ i, ∑ o, kernel i o * (if accepted i o then score i o else 0) = q i * loss i

variable {I O : Type} [Fintype I] [Fintype O] [DecidableEq I]

def Feedback.round (f : Feedback I O) (p : Dist I) : RandomObservation.Round I O :=
  { f with p := p.val, p_nonneg := p.nonneg, p_sum := p.sum_one }

def normalizer (p : Dist I) (z : I → ℝ) (η : ℝ) : ℝ :=
  ∑ i, p.val i * Real.exp (-η*z i)

theorem normalizer_pos (p : Dist I) (z : I → ℝ) (η : ℝ) :
    0 < normalizer p z η := by
  have hex : ∃ i, 0 < p.val i := by
    by_contra hn
    have hz : ∀ i, p.val i = 0 := by
      intro i
      exact le_antisymm (le_of_not_gt (fun h => hn ⟨i,h⟩)) (p.nonneg i)
    have h := p.sum_one
    simp [hz] at h
  obtain ⟨i,hi⟩ := hex
  exact Finset.sum_pos' (fun j _ => mul_nonneg (p.nonneg j) (Real.exp_pos _).le)
    ⟨i, Finset.mem_univ i, mul_pos hi (Real.exp_pos _)⟩

def update (p : Dist I) (z : I → ℝ) (η : ℝ) (P : I → Dist I) : Dist I where
  val j := (∑ i, p.val i*Real.exp (-η*z i)*(P i).val j)/normalizer p z η
  nonneg j := div_nonneg (Finset.sum_nonneg fun i _ =>
    mul_nonneg (mul_nonneg (p.nonneg i) (Real.exp_pos _).le) ((P i).nonneg j))
    (normalizer_pos p z η).le
  sum_one := by
    rw [← Finset.sum_div, Finset.sum_comm]
    simp_rw [← Finset.mul_sum, Dist.sum_one, mul_one]
    exact div_self (normalizer_pos p z η).ne'

structure Program (I O : Type) [Fintype I] [Fintype O] where
  initial : Dist I
  feedback : (n : ℕ) → Hist (I × O) n → Feedback I O
  transition : (n : ℕ) → Hist (I × O) (n+1) → I → Dist I
  η : ℝ
  rate_pos : 0 < η

def Program.state (A : Program I O) : (n : ℕ) → Hist (I × O) n → Dist I
  | 0, _ => A.initial
  | n+1, h =>
    let p := A.state n h.1
    let f := (A.feedback n h.1).round p
    update p (f.estimate h.2.1 h.2.2) A.η (A.transition n h)

def Program.round (A : Program I O) (n : ℕ) (h : Hist (I × O) n) :=
  (A.feedback n h).round (A.state n h)

def Program.kernel (A : Program I O) (n : ℕ) (h : Hist (I × O) n) (a : I × O) : ℝ :=
  (A.state n h).val a.1 * (A.feedback n h).kernel a.1 a.2

theorem Program.kernel_nonneg (A : Program I O) (n : ℕ) (h : Hist (I × O) n) (a : I × O) :
    0 ≤ A.kernel n h a :=
  mul_nonneg ((A.state n h).nonneg a.1) ((A.feedback n h).kernel_nonneg a.1 a.2)

theorem Program.kernel_sum (A : Program I O) (n : ℕ) (h : Hist (I × O) n) :
    ∑ a, A.kernel n h a = 1 := by
  simp [kernel, Fintype.sum_prod_type, ← Finset.mul_sum,
    Feedback.kernel_sum, Dist.sum_one]

theorem Program.law_normalized (A : Program I O) (N : ℕ) :
    ∑ h, pathLaw A.kernel N h = 1 :=
  pathLaw_normalized A.kernel A.kernel_sum N

theorem Program.law_nonneg (A : Program I O) (N : ℕ) (h : Hist (I × O) N) :
    0 ≤ pathLaw A.kernel N h := pathLaw_nonneg A.kernel A.kernel_nonneg N h

theorem update_comparison (p : Dist I) (z : I → ℝ) (η : ℝ) (P : I → Dist I)
    (hη : 0 < η) (hz : ∀ i, 0 ≤ z i) (i j : I)
    (hi : 0 < p.val i) (hij : 0 < (P i).val j) :
    0 < (update p z η P).val j ∧
    η*(DRGPR.mean p.val z-z i) ≤
      Real.log ((update p z η P).val j)-Real.log (p.val i)-Real.log ((P i).val j)
      +η^2/2*DRGPR.mean p.val (fun k => (z k)^2) := by
  have hZ := normalizer_pos p z η
  have hprod := mul_pos (mul_pos hi (Real.exp_pos (-η*z i))) hij
  have hs : p.val i*Real.exp (-η*z i)*(P i).val j ≤
      ∑ k, p.val k*Real.exp (-η*z k)*(P k).val j :=
    Finset.single_le_sum (fun k _ => mul_nonneg
      (mul_nonneg (p.nonneg k) (Real.exp_pos (-η*z k)).le) ((P k).nonneg j)) (Finset.mem_univ i)
  have hnum := lt_of_lt_of_le hprod hs
  have hj : 0 < (update p z η P).val j := div_pos hnum hZ
  refine ⟨hj, ?_⟩
  have hl := Real.log_le_log (div_pos hprod hZ) (div_le_div_of_nonneg_right hs hZ.le)
  change Real.log (p.val i*Real.exp (-η*z i)*(P i).val j/normalizer p z η) ≤
    Real.log ((update p z η P).val j) at hl
  rw [Real.log_div hprod.ne' hZ.ne',
    Real.log_mul (mul_pos hi (Real.exp_pos _)).ne' hij.ne',
    Real.log_mul hi.ne' (Real.exp_pos _).ne', Real.log_exp] at hl
  have hu := DRGPR.log_normalizer p.val z η hη p.nonneg p.sum_one hz
  change Real.log (normalizer p z η) ≤ _ at hu
  nlinarith

namespace Program

variable (A : Program I O) (v : (n : ℕ) → Hist (I × O) n → I)

def estimatedGap (n : ℕ) (h : Hist (I × O) n) (a : I × O) : ℝ :=
  DRGPR.mean (A.state n h).val ((A.round n h).estimate a.1 a.2)
    -(A.round n h).estimate a.1 a.2 (v n h)

def actualGap (n : ℕ) (h : Hist (I × O) n) (a : I × O) : ℝ :=
  (A.feedback n h).loss a.1-(A.feedback n h).loss (v n h)

def second (n : ℕ) (h : Hist (I × O) n) (a : I × O) : ℝ :=
  DRGPR.mean (A.state n h).val (fun i => ((A.round n h).estimate a.1 a.2 i)^2)

def codeIncrement (n : ℕ) (h : Hist (I × O) n) (a : I × O) : ℝ :=
  -Real.log ((A.transition n (h,a) (v n h)).val (v (n+1) (h,a)))

def capacity (N : ℕ) : ℝ := ∑ n ∈ Finset.range N, ∑ h,
  pathLaw A.kernel n h * ((A.feedback n h).d^2 * (A.round n h).burden)

theorem bridge_active
    (hinit : 0 < A.initial.val (v 0 ()))
    (htrans : ∀ n (h : Hist (I × O) (n+1)),
      0 < (A.transition n h (v n h.1)).val (v (n+1) h)) :
    ∀ n h, 0 < (A.state n h).val (v n h) := by
  intro n
  induction n with
  | zero => intro h; cases h; exact hinit
  | succ n ih =>
    intro h
    exact (update_comparison (A.state n h.1) ((A.round n h.1).estimate h.2.1 h.2.2)
      A.η (A.transition n h) A.rate_pos
      (fun i => (A.round n h.1).estimate_nonneg h.2.1 i h.2.2)
      (v n h.1) (v (n+1) h) (ih h.1) (htrans n h)).1

theorem path_potential
    (hinit : 0 < A.initial.val (v 0 ()))
    (htrans : ∀ n (h : Hist (I × O) (n+1)),
      0 < (A.transition n h (v n h.1)).val (v (n+1) h)) :
    ∀ N h, A.η*cumulative (A.estimatedGap v) N h ≤
      Real.log ((A.state N h).val (v N h))-Real.log (A.initial.val (v 0 ()))
      +cumulative (A.codeIncrement v) N h+A.η^2/2*cumulative A.second N h := by
  intro N
  induction N with
  | zero => intro h; cases h; simp [cumulative, state]
  | succ n ih =>
    intro h
    have step := (update_comparison (A.state n h.1) ((A.round n h.1).estimate h.2.1 h.2.2)
      A.η (A.transition n h) A.rate_pos
      (fun i => (A.round n h.1).estimate_nonneg h.2.1 i h.2.2)
      (v n h.1) (v (n+1) h) (A.bridge_active v hinit htrans n h.1) (htrans n h)).2
    have prev := ih h.1
    change A.η*(cumulative (A.estimatedGap v) n h.1+A.estimatedGap v n h.1 h.2) ≤ _
    change A.η*A.estimatedGap v n h.1 h.2 ≤
      Real.log ((A.state (n+1) h).val (v (n+1) h))-
      Real.log ((A.state n h.1).val (v n h.1))+
      A.codeIncrement v n h.1 h.2+A.η^2/2*A.second n h.1 h.2 at step
    simp only [cumulative]
    nlinarith

theorem probability_le_one (p : Dist I) (i : I) : p.val i ≤ 1 := by
  calc
    p.val i ≤ ∑ j, p.val j := Finset.single_le_sum (fun j _ => p.nonneg j) (Finset.mem_univ i)
    _ = 1 := p.sum_one

theorem path_bound (N : ℕ) (C : ℝ)
    (hinit : 0 < A.initial.val (v 0 ()))
    (htrans : ∀ n (h : Hist (I × O) (n+1)),
      0 < (A.transition n h (v n h.1)).val (v (n+1) h))
    (hcode : ∀ h, -Real.log (A.initial.val (v 0 ()))+
      cumulative (A.codeIncrement v) N h ≤ C) (h : Hist (I × O) N) :
    A.η*cumulative (A.estimatedGap v) N h ≤ C+A.η^2/2*cumulative A.second N h := by
  have hp := A.path_potential v hinit htrans N h
  have hlog := Real.log_nonpos (A.bridge_active v hinit htrans N h).le
    (probability_le_one (A.state N h) (v N h))
  linarith [hcode h]

theorem joint_avg (n : ℕ) (h : Hist (I × O) n) (f : I → O → ℝ) :
    (∑ a : I × O, A.kernel n h a*f a.1 a.2)=(A.round n h).avg f := by
  simp [kernel, round, Feedback.round, RandomObservation.Round.avg,
    Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

theorem expected_gap (N : ℕ)
    (hactive : ∀ n h, 0 < (A.state n h).val (v n h)) :
    (∑ h, pathLaw A.kernel N h*cumulative (A.estimatedGap v) N h)=
      ∑ h, pathLaw A.kernel N h*cumulative (A.actualGap v) N h := by
  rw [expected_cumulative _ _ A.kernel_sum, expected_cumulative _ _ A.kernel_sum]
  apply Finset.sum_congr rfl
  intro n _
  apply Finset.sum_congr rfl
  intro h _
  congr 1
  change (∑ a : I × O, A.kernel n h a*
    (DRGPR.mean (A.state n h).val ((A.round n h).estimate a.1 a.2)-
      (A.round n h).estimate a.1 a.2 (v n h))) =
    ∑ a : I × O, A.kernel n h a*((A.feedback n h).loss a.1-(A.feedback n h).loss (v n h))
  rw [A.joint_avg n h (fun i o => DRGPR.mean (A.state n h).val ((A.round n h).estimate i o)-
    (A.round n h).estimate i o (v n h)),
    A.joint_avg n h (fun i _ => (A.feedback n h).loss i-(A.feedback n h).loss (v n h))]
  exact (A.round n h).regret_linear (v n h) (hactive n h)

theorem expected_second (N : ℕ) :
    (∑ h, pathLaw A.kernel N h*cumulative A.second N h) ≤ A.capacity N := by
  rw [expected_cumulative _ _ A.kernel_sum]
  apply Finset.sum_le_sum
  intro n _
  apply Finset.sum_le_sum
  intro h _
  apply mul_le_mul_of_nonneg_left _ (A.law_nonneg n h)
  change (∑ a : I × O, A.kernel n h a*
    DRGPR.mean (A.state n h).val (fun i => ((A.round n h).estimate a.1 a.2 i)^2)) ≤ _
  rw [A.joint_avg n h (fun i o =>
    DRGPR.mean (A.state n h).val (fun j => ((A.round n h).estimate i o j)^2))]
  exact (A.round n h).weighted_second

/-- Algorithm-to-expectation theorem on its recursively generated trajectory.
The assumptions are local feedback semantics and path-code feasibility,
not an expected-regret inequality or an asserted global joint law. -/
theorem regret (N : ℕ) (C : ℝ)
    (hinit : 0 < A.initial.val (v 0 ()))
    (htrans : ∀ n (h : Hist (I × O) (n+1)),
      0 < (A.transition n h (v n h.1)).val (v (n+1) h))
    (hcode : ∀ h, -Real.log (A.initial.val (v 0 ()))+
      cumulative (A.codeIncrement v) N h ≤ C) :
    (∑ h, pathLaw A.kernel N h*cumulative (A.actualGap v) N h) ≤
      C/A.η+A.η/2*A.capacity N := by
  have hp := Finset.sum_le_sum (fun h (_ : h ∈ (Finset.univ : Finset (Hist (I × O) N))) =>
    mul_le_mul_of_nonneg_left (A.path_bound v N C hinit htrans hcode h) (A.law_nonneg N h))
  have hl : (∑ h, pathLaw A.kernel N h*(A.η*cumulative (A.estimatedGap v) N h)) =
      A.η*(∑ h, pathLaw A.kernel N h*cumulative (A.actualGap v) N h) := by
    rw [← A.expected_gap v N (A.bridge_active v hinit htrans), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h _
    ring
  have hr : (∑ h, pathLaw A.kernel N h*(C+A.η^2/2*cumulative A.second N h)) =
      C+A.η^2/2*(∑ h, pathLaw A.kernel N h*cumulative A.second N h) := by
    simp only [mul_add, Finset.sum_add_distrib]
    rw [← Finset.sum_mul, A.law_normalized, one_mul, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro h _
    ring
  rw [hl,hr] at hp
  have hv := mul_le_mul_of_nonneg_left (A.expected_second N) (by positivity : 0 ≤ A.η^2/2)
  have hη := A.rate_pos
  apply (mul_le_mul_right hη).mp
  calc
    _ ≤ C+A.η^2/2*A.capacity N := by nlinarith
    _ = (C/A.η+A.η/2*A.capacity N)*A.η := by field_simp [hη.ne']; ring

end Program
end DRGPR.FiniteController
#print axioms DRGPR.FiniteController.normalizer_pos
#print axioms DRGPR.FiniteController.Program.kernel_nonneg
#print axioms DRGPR.FiniteController.Program.kernel_sum
#print axioms DRGPR.FiniteController.Program.law_normalized
#print axioms DRGPR.FiniteController.Program.law_nonneg
#print axioms DRGPR.FiniteController.update_comparison
#print axioms DRGPR.FiniteController.Program.bridge_active
#print axioms DRGPR.FiniteController.Program.path_potential
#print axioms DRGPR.FiniteController.Program.probability_le_one
#print axioms DRGPR.FiniteController.Program.path_bound
#print axioms DRGPR.FiniteController.Program.joint_avg
#print axioms DRGPR.FiniteController.Program.expected_gap
#print axioms DRGPR.FiniteController.Program.expected_second
#print axioms DRGPR.FiniteController.Program.regret
