import FiniteController

noncomputable section
open scoped BigOperators
namespace DRGPR.FiniteController.Program
open SupportedInformation
variable {I O : Type} [Fintype I] [Fintype O] [DecidableEq I]

/-- Integrate a locally proved conditional second-moment certificate. -/
theorem expected_local_second (A : Program I O)
    (V : (n : ℕ) → Hist (I × O) n → ℝ)
    (hV : ∀ n h, (A.round n h).avg (fun i o =>
      DRGPR.mean (A.state n h).val (fun j => ((A.round n h).estimate i o j)^2)) ≤ V n h)
    (N : ℕ) :
    (∑ h, pathLaw A.kernel N h*cumulative A.second N h) ≤
      ∑ n ∈ Finset.range N, ∑ h, pathLaw A.kernel n h*V n h := by
  rw [expected_cumulative _ _ A.kernel_sum]
  apply Finset.sum_le_sum
  intro n _
  apply Finset.sum_le_sum
  intro h _
  apply mul_le_mul_of_nonneg_left _ (A.law_nonneg n h)
  change (∑ a : I × O, A.kernel n h a*
    DRGPR.mean (A.state n h).val (fun j => ((A.round n h).estimate a.1 a.2 j)^2)) ≤ _
  rw [A.joint_avg n h (fun i o => DRGPR.mean (A.state n h).val
    (fun j => ((A.round n h).estimate i o j)^2))]
  exact hV n h

/-- Closed-loop selection with an arbitrary proved local variance bound.
Neither the trajectory law nor the expected regret is an assumption. -/
theorem regret_local_variance (A : Program I O)
    (v : (n : ℕ) → Hist (I × O) n → I) (N : ℕ) (C : ℝ)
    (hinit : 0 < A.initial.val (v 0 ()))
    (htrans : ∀ n (h : Hist (I × O) (n+1)),
      0 < (A.transition n h (v n h.1)).val (v (n+1) h))
    (hcode : ∀ h, -Real.log (A.initial.val (v 0 ()))+
      cumulative (A.codeIncrement v) N h ≤ C)
    (V : (n : ℕ) → Hist (I × O) n → ℝ)
    (hV : ∀ n h, (A.round n h).avg (fun i o =>
      DRGPR.mean (A.state n h).val (fun j => ((A.round n h).estimate i o j)^2)) ≤ V n h) :
    (∑ h, pathLaw A.kernel N h*cumulative (A.actualGap v) N h) ≤
      C/A.η+A.η/2*(∑ n ∈ Finset.range N, ∑ h, pathLaw A.kernel n h*V n h) := by
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
  have hv := mul_le_mul_of_nonneg_left (A.expected_local_second V hV N)
    (by positivity : 0 ≤ A.η^2/2)
  have hη := A.rate_pos
  apply (mul_le_mul_right hη).mp
  calc
    _ ≤ C+A.η^2/2*(∑ n ∈ Finset.range N, ∑ h, pathLaw A.kernel n h*V n h) := by nlinarith
    _ = (C/A.η+A.η/2*(∑ n ∈ Finset.range N, ∑ h, pathLaw A.kernel n h*V n h))*A.η := by
      field_simp [hη.ne']; ring

end DRGPR.FiniteController.Program
#print axioms DRGPR.FiniteController.Program.expected_local_second
#print axioms DRGPR.FiniteController.Program.regret_local_variance
