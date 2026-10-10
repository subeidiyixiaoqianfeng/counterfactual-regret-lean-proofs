import RestartedGrowing

noncomputable section
open scoped BigOperators
namespace DRGPR.TaskSaturation
open RestartedGrowing PhaseAlgorithm PhaseSwitching WindowLedger

/-- There are at most n-1 genuine within-phase switches. Time zero is not
a switch. This sharper fact prevents charging an extra half unit per phase. -/
theorem internal_switch_count {I : Type} [DecidableEq I] (u : ℕ → I) (n : ℕ) :
    (switches u n).card ≤ n-1 := by
  have hs : switches u n ⊆ (Finset.range n).erase 0 := by
    intro t ht
    have ht' := Finset.mem_filter.mp ht
    exact Finset.mem_erase.mpr ⟨by omega,ht'.1⟩
  have hc := Finset.card_le_card hs
  by_cases hn : n=0
  · subst n; simp [switches]
  · have hzero : 0 ∈ Finset.range n := Finset.mem_range.mpr (by omega)
    simpa [Finset.card_erase_of_mem hzero] using hc

theorem phase_base_bounds (M : Model) (r : ℕ) (a : M.Record r) :
    0 ≤ learnerTotal M.n (M.b r) (M.loss r) a ∧
      learnerTotal M.n (M.b r) (M.loss r) a ≤ M.n := by
  constructor
  · exact Finset.sum_nonneg (fun t _ => M.loss_nonneg r _ t)
  · calc
      _ ≤ ∑ _t : Fin M.n, (1:ℝ) := Finset.sum_le_sum (fun t _ => M.loss_le r _ t)
      _ = _ := by simp

theorem stage_bounds (M : Model) (r : ℕ) (h : M.Past r) (a : M.Record r) :
    0 ≤ M.stage r h a ∧ M.stage r h a ≤ M.n := by
  have hb := phase_base_bounds M r a
  have hs := internal_switch_count (played M.n (M.b r) a (M.fallback r)) M.n
  have hsR : ((switches (played M.n (M.b r) a (M.fallback r)) M.n).card:ℝ) ≤ (M.n:ℝ)-1 := by
    have hn : 1 ≤ M.n := M.n_pos
    have hcast : ((switches (played M.n (M.b r) a (M.fallback r)) M.n).card:ℝ)+1 ≤ M.n := by
      exact_mod_cast (show (switches (played M.n (M.b r) a (M.fallback r)) M.n).card+1 ≤ M.n by omega)
    linarith
  have hsn : (0:ℝ) ≤ (switches (played M.n (M.b r) a (M.fallback r)) M.n).card := Nat.cast_nonneg _
  have hd := M.boundary_bounds r h a
  unfold Model.stage Model.phaseCost taskTotal
  constructor <;> linarith

theorem learner_range (M : Model) (m : ℕ) :
    0 ≤ M.learnerCost m ∧ M.learnerCost m ≤ (m:ℝ)*M.n := by
  have hu := DependentBlocks.expected_total_le M.kernel M.stage M.kernel_nonneg
    M.kernel_normalized (fun _ => (M.n:ℝ)) (fun r h => by
      calc
        _ ≤ ∑ a, M.kernel r h a*(M.n:ℝ) := Finset.sum_le_sum (fun a _ =>
          mul_le_mul_of_nonneg_left (stage_bounds M r h a).2 (M.kernel_nonneg r h a))
        _ = _ := by rw [← Finset.sum_mul,M.kernel_normalized,one_mul]) m
  have ht : ∀ r (h : M.Past r), 0 ≤ DependentBlocks.total M.stage r h := by
    intro r
    induction r with
    | zero => intro h; exact le_rfl
    | succ r ih =>
      intro h
      exact add_nonneg (ih h.1) (stage_bounds M r h.1 h.2).1
  constructor
  · exact Finset.sum_nonneg (fun h _ => mul_nonneg
      (DependentBlocks.nonneg M.kernel M.kernel_nonneg m h) (ht m h))
  · simpa [Model.learnerCost] using hu

theorem comparator_nonneg (M : Model) (v : (r : ℕ) → Fin (M.K r)) (m : ℕ) :
    0 ≤ M.comparatorCost v m := by
  apply le_trans _ (M.comparator_base_le v m)
  exact Finset.sum_nonneg (fun r _ => div_nonneg
    (Finset.sum_nonneg (fun t _ => M.loss_nonneg r (v r) t)) (by norm_num))

theorem actual_regret_le_horizon (M : Model) (m : ℕ) :
    M.learnerCost m-sInf (Set.range (fun v : (r : ℕ) → Fin (M.K r) => M.comparatorCost v m)) ≤
      (m:ℝ)*M.n := by
  apply DRGPR.infimum_transfer
  · exact ⟨M.comparatorCost M.fallback m,⟨M.fallback,rfl⟩⟩
  · intro x hx
    obtain ⟨v,rfl⟩ := hx
    linarith [(learner_range M m).2,comparator_nonneg M v m]

end DRGPR.TaskSaturation
#print axioms DRGPR.TaskSaturation.internal_switch_count
#print axioms DRGPR.TaskSaturation.phase_base_bounds
#print axioms DRGPR.TaskSaturation.stage_bounds
#print axioms DRGPR.TaskSaturation.learner_range
#print axioms DRGPR.TaskSaturation.comparator_nonneg
#print axioms DRGPR.TaskSaturation.actual_regret_le_horizon
