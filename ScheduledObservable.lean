import RestartedGrowing

noncomputable section
namespace DRGPR.ScheduledObservable
open RestartedGrowing SupportedInformation PhaseAlgorithm PhaseSchedule VariableRunController

/-- The actual phase state is a function of received identity/score pairs only.
The hidden loss table enters the environment that emits scores, not the update. -/
theorem phase_state_observable (M : Model) (r s : ℕ)
    (h : Hist (Fin (M.K r) × (Fin M.n → Bool)) s) :
    (M.phase r).state s h =
      GranularObservable.visibleState (M.η r)
        (uniform (by simpa using M.K_pos r)) s
        (GranularObservable.received M.q
          (fun t _ => masked (slots M.n (M.b r) t) (M.loss r)) s h) := by
  exact GranularObservable.state_factors_through_received M.q M.q_pos M.q_le
    (M.η r) (M.eta_pos r) (uniform (by simpa using M.K_pos r))
    (fun t _ => masked (slots M.n (M.b r) t) (M.loss r))
    (fun t _ => masked_nonneg _ _ (M.loss_nonneg r))
    (fun t _ => masked_le_one _ _ (M.loss_le r)) s h

/-- Within a phase, identical received histories induce identical next laws,
even when latent erasure masks differ. -/
theorem same_received_same_choice (M : Model) (r s : ℕ)
    (h h' : Hist (Fin (M.K r) × (Fin M.n → Bool)) s)
    (he : GranularObservable.received M.q
      (fun t _ => masked (slots M.n (M.b r) t) (M.loss r)) s h =
      GranularObservable.received M.q
      (fun t _ => masked (slots M.n (M.b r) t) (M.loss r)) s h') :
    (M.phase r).state s h=(M.phase r).state s h' := by
  rw [phase_state_observable,phase_state_observable,he]

end DRGPR.ScheduledObservable
#print axioms DRGPR.ScheduledObservable.phase_state_observable
#print axioms DRGPR.ScheduledObservable.same_received_same_choice
