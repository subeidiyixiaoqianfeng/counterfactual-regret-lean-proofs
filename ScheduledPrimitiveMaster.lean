import PrimitiveRegret

noncomputable section
open scoped BigOperators
namespace DRGPR.ScheduledPrimitiveMaster
open SupportedInformation

/-- Public parameters alone construct the learner. In particular, there is
no loss table or target identity parameter in this constructor. -/
def master (K : ℕ → ℕ) (n : ℕ) (q : ℝ) (hK : ∀ r, 2 ≤ K r) : GrowingInformation.Master K n where
  policy r _ := PrimitiveRun.algorithm q
    (TunedPhase.rate (Real.log (K r))
      (TunedPhase.varianceBudget n (TunedPhase.runCap n (K r)) (K r) q))
    (TunedPhase.runCap n (K r))
    (PhaseAlgorithm.uniform (by
      simpa using (show (0:ℝ) < K r by exact_mod_cast (by have := hK r; omega : 0 < K r))))
    ⟨0,by have := hK r; omega⟩

theorem phase_reset (K : ℕ → ℕ) (n : ℕ) (q : ℝ) (hK : ∀ r, 2 ≤ K r) (r : ℕ)
    (h g : DependentBlocks.History (fun s => MultiphaseOblivious.Transcript (Fin (K s)) n) r) :
    (master K n q hK).policy r h=(master K n q hK).policy r g := rfl

theorem first_draw_uniform (K : ℕ → ℕ) (n : ℕ) (q : ℝ) (hK : ∀ r, 2 ≤ K r) (r : ℕ)
    (h : DependentBlocks.History (fun s => MultiphaseOblivious.Transcript (Fin (K s)) n) r)
    (i : Fin (K r)) : ((master K n q hK).policy r h).p 0 () i=1/(K r:ℝ) := by
  simp [master,PrimitiveRun.algorithm,PrimitiveRun.distribution,PrimitiveRun.state,
    PrimitiveRun.initialState,PhaseAlgorithm.uniform]

/-- The public construction uses the exact cap, rate and initial distribution
of the scheduled upper model. This lemma identifies parameters, not yet the
complete scheduled regret bound. -/
theorem parameters_match (M : RestartedGrowing.Model) (r : ℕ)
    (h : DependentBlocks.History
      (fun s => MultiphaseOblivious.Transcript (Fin (M.K s)) M.n) r) :
    (master M.K M.n M.q M.K_two).policy r h=
      PrimitiveRun.algorithm M.q (M.η r) (M.b r)
        (PhaseAlgorithm.uniform (by simpa using M.K_pos r)) (M.fallback r) := rfl

/-- The primitive implementation is actually a member of the causal class
quantified over by the information lower theorem. No oracle conversion is
supplied as a premise to this application. -/
theorem information_instance (K : ℕ → ℕ) (n m : ℕ) (q : ℝ)
    (hK : ∀ r, 2 ≤ K r) (hn : 0 < n) (hq : 0 < q) (hq1 : q ≤ 1) :
    ∃ e : DependentBlocks.History (fun r => MultiphaseOblivious.Table (Fin (K r)) n) m,
      (∑ r ∈ Finset.range m, GrowingInformation.lower K n q r)/2-(m:ℝ)/2 ≤
        GrowingTaskLower.regret hK (master K n q hK) q m e :=
  GrowingTaskLower.fixed_table_lower (master K n q hK) q m hn hK hq hq1

end DRGPR.ScheduledPrimitiveMaster
#print axioms DRGPR.ScheduledPrimitiveMaster.phase_reset
#print axioms DRGPR.ScheduledPrimitiveMaster.first_draw_uniform
#print axioms DRGPR.ScheduledPrimitiveMaster.parameters_match
#print axioms DRGPR.ScheduledPrimitiveMaster.information_instance
