import DRGPR

/-!
Deterministic selection core on time-varying finite identity types.
Indices start at 0. The type `ι r` can grow with r; no enumeration of future
identities is required by the recurrence. Transition row sums are hypotheses,
not the regret conclusion. Stochastic lifting and deployment are NOT here.
-/
noncomputable section
open scoped BigOperators
namespace DRGPR.Growing

variable {ι : ℕ → Type*} [∀ r, Fintype (ι r)]

def mass (ν : ι 0 → ℝ) (P : ∀ r, ι r → ι (r+1) → ℝ)
    (z : ∀ r, ι r → ℝ) (η : ℝ) : ∀ r, ι r → ℝ
  | 0 => ν
  | r+1 => fun j => ∑ i, mass ν P z η r i * Real.exp (-η * z r i) * P r i j

def total (ν : ι 0 → ℝ) (P : ∀ r, ι r → ι (r+1) → ℝ)
    (z : ∀ r, ι r → ℝ) (η : ℝ) (r : ℕ) : ℝ := ∑ i, mass ν P z η r i

def prob (ν : ι 0 → ℝ) (P : ∀ r, ι r → ι (r+1) → ℝ)
    (z : ∀ r, ι r → ℝ) (η : ℝ) (r : ℕ) (i : ι r) : ℝ :=
  mass ν P z η r i / total ν P z η r

variable (ν : ι 0 → ℝ) (P : ∀ r, ι r → ι (r+1) → ℝ)
  (z : ∀ r, ι r → ℝ) (η : ℝ)
  (hν : ∀ i, 0 ≤ ν i) (hνsum : ∑ i, ν i = 1)
  (hP : ∀ r i j, 0 ≤ P r i j) (hPsum : ∀ r i, ∑ j, P r i j = 1)

include hν hP in
theorem mass_nonneg (r : ℕ) (i : ι r) : 0 ≤ mass ν P z η r i := by
  induction r with
  | zero => exact hν i
  | succ r ih =>
    exact Finset.sum_nonneg fun j _ =>
      mul_nonneg (mul_nonneg (ih j) (Real.exp_pos _).le) (hP r j i)

include hPsum in
theorem total_step (r : ℕ) :
    total ν P z η (r+1) = ∑ i, mass ν P z η r i * Real.exp (-η * z r i) := by
  exact DRGPR.transition_mass _ _ (hPsum r)

include hν hνsum hP hPsum in
theorem total_pos (r : ℕ) : 0 < total ν P z η r := by
  induction r with
  | zero => simpa [total, mass, hνsum]
  | succ r ih =>
    rw [total_step ν P z η hPsum r]
    have hex : ∃ i, 0 < mass ν P z η r i := by
      by_contra hn
      have hz : ∀ i, mass ν P z η r i = 0 := by
        intro i
        have hn' : ¬ 0 < mass ν P z η r i := fun hi => hn ⟨i, hi⟩
        exact le_antisymm (le_of_not_gt hn') (mass_nonneg ν P z η hν hP r i)
      simp [total, hz] at ih
    obtain ⟨i, hi⟩ := hex
    exact Finset.sum_pos' (fun j _ => mul_nonneg
      (mass_nonneg ν P z η hν hP r j) (Real.exp_pos _).le)
      ⟨i, Finset.mem_univ i, mul_pos hi (Real.exp_pos _)⟩

include hν hνsum hP hPsum in
theorem prob_nonneg (r : ℕ) (i : ι r) : 0 ≤ prob ν P z η r i := by
  exact div_nonneg (mass_nonneg ν P z η hν hP r i)
    (total_pos ν P z η hν hνsum hP hPsum r).le

include hν hνsum hP hPsum in
theorem prob_sum (r : ℕ) : ∑ i, prob ν P z η r i = 1 := by
  simp only [prob, ← Finset.sum_div]
  exact div_self (total_pos ν P z η hν hνsum hP hPsum r).ne'

include hν hνsum hP hPsum in
theorem total_factor (r : ℕ) :
    total ν P z η (r+1) = total ν P z η r *
      (∑ i, prob ν P z η r i * Real.exp (-η * z r i)) := by
  rw [total_step ν P z η hPsum r, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  dsimp [prob]
  field_simp [(total_pos ν P z η hν hνsum hP hPsum r).ne']

include hν hνsum hP hPsum in
theorem log_total_step (hη : 0 < η) (hz : ∀ r i, 0 ≤ z r i) (r : ℕ) :
    Real.log (total ν P z η (r+1)) ≤ Real.log (total ν P z η r)
      - η * DRGPR.mean (prob ν P z η r) (z r)
      + η^2/2 * DRGPR.mean (prob ν P z η r) (fun i => z r i ^ 2) := by
  have hp := total_pos ν P z η hν hνsum hP hPsum r
  have hpnext := total_pos ν P z η hν hνsum hP hPsum (r+1)
  have hf := total_factor ν P z η hν hνsum hP hPsum r
  have hn : 0 < ∑ i, prob ν P z η r i * Real.exp (-η * z r i) := by
    rw [hf] at hpnext
    exact (mul_pos_iff_of_pos_left hp).mp hpnext
  rw [hf, Real.log_mul hp.ne' hn.ne']
  have hu := DRGPR.log_normalizer (prob ν P z η r) (z r) η hη
    (prob_nonneg ν P z η hν hνsum hP hPsum r)
    (prob_sum ν P z η hν hνsum hP hPsum r) (hz r)
  linarith

include hν hνsum hP hPsum in
theorem log_total_upper (hη : 0 < η) (hz : ∀ r i, 0 ≤ z r i) (R : ℕ) :
    Real.log (total ν P z η R) ≤
      -η * (∑ r ∈ Finset.range R, DRGPR.mean (prob ν P z η r) (z r))
      + η^2/2 * (∑ r ∈ Finset.range R,
          DRGPR.mean (prob ν P z η r) (fun i => z r i ^ 2)) := by
  induction R with
  | zero => simp [total, mass, hνsum]
  | succ R ih =>
    have hs := log_total_step ν P z η hν hνsum hP hPsum hη hz R
    simp only [Finset.sum_range_succ]
    nlinarith

/- The single-path term is derived from the recurrence, not assumed. -/
include hν hP in
theorem path_log_lower (v : ∀ r, ι r) (hv0 : 0 < ν (v 0))
    (hvP : ∀ r, 0 < P r (v r) (v (r+1))) (R : ℕ) :
    0 < mass ν P z η R (v R) ∧
    Real.log (ν (v 0)) +
      (∑ r ∈ Finset.range R, (Real.log (P r (v r) (v (r+1))) - η * z r (v r)))
      ≤ Real.log (mass ν P z η R (v R)) := by
  classical
  induction R with
  | zero => simpa [mass] using And.intro hv0 (le_refl (Real.log (ν (v 0))))
  | succ R ih =>
    have hs : mass ν P z η R (v R) * Real.exp (-η * z R (v R)) *
        P R (v R) (v (R+1)) ≤ mass ν P z η (R+1) (v (R+1)) := by
      change _ ≤ ∑ i, mass ν P z η R i * Real.exp (-η * z R i) * P R i (v (R+1))
      exact Finset.single_le_sum (fun i _ => mul_nonneg
        (mul_nonneg (mass_nonneg ν P z η hν hP R i) (Real.exp_pos (-η * z R i)).le)
        (hP R i (v (R+1)))) (Finset.mem_univ (v R))
    have hprod := mul_pos (mul_pos ih.1 (Real.exp_pos (-η * z R (v R)))) (hvP R)
    refine ⟨lt_of_lt_of_le hprod hs, ?_⟩
    have hl := Real.log_le_log hprod hs
    rw [Real.log_mul (mul_pos ih.1 (Real.exp_pos _)).ne' (hvP R).ne',
      Real.log_mul ih.1.ne' (Real.exp_pos _).ne', Real.log_exp] at hl
    rw [Finset.sum_range_succ]
    linarith [ih.2]

/- Terminal transition row sums remove any artificial final switching charge. -/
include hν hP hPsum in
theorem terminal_log_lower (v : ∀ r, ι r) (hv0 : 0 < ν (v 0))
    (hvP : ∀ r, 0 < P r (v r) (v (r+1))) (R : ℕ) :
    Real.log (ν (v 0)) +
      (∑ r ∈ Finset.range R, Real.log (P r (v r) (v (r+1))))
      - η * (∑ r ∈ Finset.range (R+1), z r (v r))
      ≤ Real.log (total ν P z η (R+1)) := by
  classical
  have hpath := path_log_lower ν P z η hν hP v hv0 hvP R
  have hs : mass ν P z η R (v R) * Real.exp (-η * z R (v R)) ≤
      total ν P z η (R+1) := by
    rw [total_step ν P z η hPsum R]
    exact Finset.single_le_sum (fun i _ =>
      mul_nonneg (mass_nonneg ν P z η hν hP R i) (Real.exp_pos (-η * z R i)).le)
      (Finset.mem_univ (v R))
  have hl := Real.log_le_log (mul_pos hpath.1 (Real.exp_pos _)) hs
  rw [Real.log_mul hpath.1.ne' (Real.exp_pos _).ne', Real.log_exp] at hl
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum] at hpath
  rw [Finset.sum_range_succ]
  nlinarith [hpath.2]

/- Complete deterministic growing-path potential bound, for R+1 loss updates. -/
include hν hνsum hP hPsum in
theorem growing_path_regret (hη : 0 < η) (hz : ∀ r i, 0 ≤ z r i)
    (v : ∀ r, ι r) (hv0 : 0 < ν (v 0))
    (hvP : ∀ r, 0 < P r (v r) (v (r+1))) (R : ℕ) :
    (∑ r ∈ Finset.range (R+1), DRGPR.mean (prob ν P z η r) (z r))
      - (∑ r ∈ Finset.range (R+1), z r (v r)) ≤
    -(Real.log (ν (v 0)) +
        ∑ r ∈ Finset.range R, Real.log (P r (v r) (v (r+1)))) / η
      + η/2 * (∑ r ∈ Finset.range (R+1),
          DRGPR.mean (prob ν P z η r) (fun i => z r i ^ 2)) := by
  exact DRGPR.potential_rearrange η (Real.log (total ν P z η (R+1)))
    _ _ _ _ hη
    (terminal_log_lower ν P z η hν hP hPsum v hv0 hvP R)
    (log_total_upper ν P z η hν hνsum hP hPsum hη hz (R+1))

end DRGPR.Growing

#print axioms DRGPR.Growing.mass_nonneg
#print axioms DRGPR.Growing.total_step
#print axioms DRGPR.Growing.total_pos
#print axioms DRGPR.Growing.prob_nonneg
#print axioms DRGPR.Growing.prob_sum
#print axioms DRGPR.Growing.total_factor
#print axioms DRGPR.Growing.log_total_step
#print axioms DRGPR.Growing.log_total_upper
#print axioms DRGPR.Growing.path_log_lower
#print axioms DRGPR.Growing.terminal_log_lower
#print axioms DRGPR.Growing.growing_path_regret
