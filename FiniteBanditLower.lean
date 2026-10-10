import InformationRate

noncomputable section
open scoped BigOperators
namespace DRGPR.FiniteBanditLower
open DRGPR.SupportedInformation DRGPR.ErasedBandit DRGPR.InformationRate

theorem sum_counts {I : Type} [Fintype I] [DecidableEq I] :
    ∀ n (h : Hist (I × Option Bool) n), (∑ j, counts j n h)=(n:ℝ) := by
  intro n
  induction n with
  | zero => intro h; simp [counts, cumulative]
  | succ n ih =>
    intro h
    change (∑ j, (counts j n h.1 + (if h.2.1=j then 1 else 0)))=(n+1:ℕ)
    rw [Finset.sum_add_distrib, ih]
    simp

theorem base_independent {I : Type} [DecidableEq I] (p : I → ℝ) (q : ℝ) (i j : I) :
    joint p q 0 i=joint p q 0 j := by
  funext x
  simp [joint]

theorem single_phase {I : Type} [Fintype I] [DecidableEq I]
    (p : (n : ℕ) → Hist (I × Option Bool) n → I → ℝ)
    (hp : ∀ n h i, 0 ≤ p n h i) (hp1 : ∀ n h, ∑ i, p n h i=1)
    (q : ℝ) (N : ℕ) (hN : 0 < N) (j₀ : I)
    (hK : (2:ℝ) ≤ Fintype.card I) (hq : 0 < q) (hq1 : q ≤ 1) :
    let e := gap (Fintype.card I) q N
    (1/32:ℝ)*min (N:ℝ) (Real.sqrt ((Fintype.card I)*N/q)) ≤
      e*((N:ℝ)-(∑ j, ∑ h, pathLaw (fun n h => joint (p n h) q e j) N h*counts j N h)/
        (Fintype.card I:ℝ)) := by
  dsimp only
  let k := fun n h => joint (p n h) q 0 j₀
  let x := fun j => ∑ h, pathLaw k N h*counts j N h
  let e := gap (Fintype.card I) q N
  let y := fun j => ∑ h, pathLaw (fun n h => joint (p n h) q e j) N h*counts j N h
  have hn : (0:ℝ) < N := by exact_mod_cast hN
  have hk0 : (0:ℝ) < Fintype.card I := by linarith
  have he := gap_properties (Fintype.card I) q N hk0 hq hn
  have hk := fun n h => joint_nonneg (p n h) q 0 j₀ (hp n h) hq hq1 (le_refl 0) (by norm_num)
  have hks := fun n h => ErasedBandit.joint_normalized (p n h) q 0 j₀ (hp1 n h)
  have hx : ∀ j, 0 ≤ x j := by
    intro j
    exact Finset.sum_nonneg (fun h _ => mul_nonneg (pathLaw_nonneg k hk N h) (count_bounds j N h).1)
  have hxs : ∑ j, x j=(N:ℝ) := by
    dsimp [x]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, sum_counts, ← Finset.sum_mul, pathLaw_normalized k hks, one_mul]
  have hy : ∀ j, y j ≤ x j+(N:ℝ)*Real.sqrt (4*q*e^2*x j) := by
    intro j
    have ht := count_compare p hp hp1 q e j N hN hq hq1 he.1 he.2.1
    have hkEq : (fun n h => joint (p n h) q 0 j)=k := by
      funext n h
      exact base_independent (p n h) q j j₀
    rw [hkEq] at ht
    exact ht
  exact information_lower_from_counts x y N q hK hn hq hx hxs hy

end DRGPR.FiniteBanditLower
#print axioms DRGPR.FiniteBanditLower.sum_counts
#print axioms DRGPR.FiniteBanditLower.base_independent
#print axioms DRGPR.FiniteBanditLower.single_phase
