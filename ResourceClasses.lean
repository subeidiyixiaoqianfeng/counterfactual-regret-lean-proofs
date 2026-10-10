import NativeSemantics

noncomputable section
open MeasureTheory
namespace DRGPR.ResourceClasses
open NativeSemantics
variable {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
variable {T : ℕ} {M : Type*}

/-- All restrictions other than the resource mode are held fixed. Costs are
measured on the candidate's own trajectory. The prefix index includes zero. -/
def hardClass (C : M → Execution X T) (allowed : Set M)
    (cost : M → Fin (T+1) → ((n : ℕ) → X n) → ℝ) (B : Fin (T+1) → ℝ) : Set M :=
  {m | m ∈ allowed ∧ ∀ᵐ h ∂(C m).law, ∀ s, cost m s h ≤ B s}

def meanClass (C : M → Execution X T) (allowed : Set M)
    (cost : M → Fin (T+1) → ((n : ℕ) → X n) → ℝ) (B : Fin (T+1) → ℝ) : Set M :=
  {m | m ∈ allowed ∧ ∀ s, (∫ h, cost m s h ∂(C m).law) ≤ B s}

theorem hard_subset_mean (C : M → Execution X T) (allowed : Set M)
    (cost : M → Fin (T+1) → ((n : ℕ) → X n) → ℝ) (B : Fin (T+1) → ℝ)
    (hc : ∀ m ∈ allowed, ∀ s, Integrable (cost m s) (C m).law) :
    hardClass C allowed cost B ⊆ meanClass C allowed cost B := by
  intro m hm
  refine ⟨hm.1, ?_⟩
  intro s
  have hp : ∀ᵐ h ∂(C m).law, cost m s h ≤ B s :=
    hm.2.mono (fun _ hh => hh s)
  have h := integral_mono_ae (hc m hm.1 s) (integrable_const (B s)) hp
  simpa using h

def values (C : M → Execution X T) (S : Set M) : Set ℝ :=
  (fun m => (C m).expectedLoss) '' S

theorem values_bounded_below (C : M → Execution X T) (S : Set M) :
    BddBelow (values C S) := by
  refine ⟨0, ?_⟩
  intro x hx
  obtain ⟨m, _, rfl⟩ := hx
  exact (C m).expected_bounds.1

theorem optimal_value_antitone (C : M → Execution X T)
    (S R : Set M) (hS : S.Nonempty) (hSR : S ⊆ R) :
    sInf (values C R) ≤ sInf (values C S) := by
  apply le_csInf (hS.image _)
  intro x hx
  apply csInf_le (values_bounded_below C R)
  obtain ⟨m, hm, rfl⟩ := hx
  exact ⟨m, hSR hm, rfl⟩

theorem budget_penalty_nonneg (C : M → Execution X T) (allowed : Set M)
    (cost : M → Fin (T+1) → ((n : ℕ) → X n) → ℝ) (B : Fin (T+1) → ℝ)
    (hc : ∀ m ∈ allowed, ∀ s, Integrable (cost m s) (C m).law)
    (hne : (hardClass C allowed cost B).Nonempty) :
    0 ≤ sInf (values C (hardClass C allowed cost B)) -
      sInf (values C (meanClass C allowed cost B)) := by
  exact sub_nonneg.mpr
    (optimal_value_antitone C _ _ hne (hard_subset_mean C allowed cost B hc))

/-- The budget penalty changes the comparator optimum. It is not a second
charge for tokens already accounted for by resource feasibility. -/
theorem comparator_change_identity (C : M → Execution X T)
    (A : Execution X T) (hard mean : Set M) :
    A.expectedLoss - sInf (values C mean) =
      (A.expectedLoss - sInf (values C hard)) +
      (sInf (values C hard) - sInf (values C mean)) := by ring

end DRGPR.ResourceClasses
#print axioms DRGPR.ResourceClasses.hard_subset_mean
#print axioms DRGPR.ResourceClasses.values_bounded_below
#print axioms DRGPR.ResourceClasses.optimal_value_antitone
#print axioms DRGPR.ResourceClasses.budget_penalty_nonneg
#print axioms DRGPR.ResourceClasses.comparator_change_identity
