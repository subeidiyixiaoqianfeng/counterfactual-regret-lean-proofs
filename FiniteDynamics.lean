import FiniteTV

noncomputable section
open scoped BigOperators
namespace DRGPR.FiniteDynamics
open FiniteTV
variable {I J : Type} [Fintype I] [Fintype J]

theorem markov_nonexpansive (p q : FiniteController.Dist I)
    (K : I → FiniteController.Dist J) : tv (push p K) (push q K) ≤ tv p q := by
  have hj (j : J) : |(push p K).val j-(push q K).val j| ≤
      ∑ i, |p.val i-q.val i| * (K i).val j := by
    change |(∑ i, p.val i*(K i).val j)-(∑ i, q.val i*(K i).val j)| ≤ _
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ i, |p.val i*(K i).val j-q.val i*(K i).val j| := Finset.abs_sum_le_sum_abs _ _
      _ = _ := by simp_rw [← sub_mul,abs_mul,abs_of_nonneg ((K _).nonneg _)]
  have hh := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset J)) => hj j)
  rw [Finset.sum_comm] at hh
  simp only [← Finset.mul_sum,FiniteController.Dist.sum_one,mul_one] at hh
  exact div_le_div_of_nonneg_right hh (by norm_num)

def blend (α : ℝ) (h0 : 0 ≤ α) (h1 : α ≤ 1)
    (r p : FiniteController.Dist I) : FiniteController.Dist I where
  val i := α*r.val i+(1-α)*p.val i
  nonneg i := add_nonneg (mul_nonneg h0 (r.nonneg i))
    (mul_nonneg (sub_nonneg.mpr h1) (p.nonneg i))
  sum_one := by rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum,r.sum_one,p.sum_one]; ring

theorem blend_tv (α : ℝ) (h0 : 0 ≤ α) (h1 : α ≤ 1)
    (r p q : FiniteController.Dist I) :
    tv (blend α h0 h1 r p) (blend α h0 h1 r q)=(1-α)*tv p q := by
  have he (i : I) : (blend α h0 h1 r p).val i-(blend α h0 h1 r q).val i=
      (1-α)*(p.val i-q.val i) := by dsimp [blend]; ring
  unfold tv
  simp_rw [he,abs_mul,abs_of_nonneg (sub_nonneg.mpr h1)]
  rw [← Finset.mul_sum]
  ring

theorem push_blend (p : FiniteController.Dist I) (α : ℝ) (h0 : 0 ≤ α) (h1 : α ≤ 1)
    (r : FiniteController.Dist J) (K : I → FiniteController.Dist J) :
    push p (fun i => blend α h0 h1 r (K i))=blend α h0 h1 r (push p K) := by
  have he : ∀ j, (push p (fun i => blend α h0 h1 r (K i))).val j=
      (blend α h0 h1 r (push p K)).val j := by
    intro j
    dsimp [push,blend]
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib]
    have hc : (∑ i, p.val i*(α*r.val j))=α*r.val j := by rw [← Finset.sum_mul,p.sum_one,one_mul]
    rw [hc,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  cases hp : push p (fun i => blend α h0 h1 r (K i))
  cases hq : blend α h0 h1 r (push p K)
  simp only [hp,hq] at he
  congr
  exact funext he

/-- A common refresh component is a proved contraction, not a scalar certificate. -/
theorem doeblin_contraction (p q : FiniteController.Dist I)
    (α : ℝ) (h0 : 0 ≤ α) (h1 : α ≤ 1) (r : FiniteController.Dist J)
    (K : I → FiniteController.Dist J) :
    tv (push p (fun i => blend α h0 h1 r (K i)))
      (push q (fun i => blend α h0 h1 r (K i))) ≤ (1-α)*tv p q := by
  rw [push_blend,push_blend,blend_tv]
  exact mul_le_mul_of_nonneg_left (markov_nonexpansive p q K) (sub_nonneg.mpr h1)

def evolve (p : FiniteController.Dist I) (K : ℕ → I → FiniteController.Dist I) :
    ℕ → FiniteController.Dist I
  | 0 => p
  | n+1 => push (evolve p K n) (K n)

theorem discrepancy_step (p : FiniteController.Dist I)
    (K L : ℕ → I → FiniteController.Dist I) (β ε : ℝ) (n : ℕ)
    (hc : ∀ a b, tv (push a (L n)) (push b (L n)) ≤ β*tv a b)
    (he : ∀ i, tv (K n i) (L n i) ≤ ε) :
    tv (evolve p K (n+1)) (evolve p L (n+1)) ≤
      β*tv (evolve p K n) (evolve p L n)+ε := by
  have ht := triangle (push (evolve p K n) (K n)) (push (evolve p K n) (L n))
    (push (evolve p L n) (L n))
  have hp := kernel_perturbation (evolve p K n) (K n) (L n) ε he
  have h := hc (evolve p K n) (evolve p L n)
  change tv (push (evolve p K n) (K n)) (push (evolve p L n) (L n)) ≤ _
  linarith

/-- Sum the derived recurrence, retaining the nonnegative terminal discrepancy. -/
theorem discrepancy_sum (p : FiniteController.Dist I)
    (K L : ℕ → I → FiniteController.Dist I) (β : ℝ) (ε : ℕ → ℝ) (N : ℕ)
    (hb : β < 1)
    (hc : ∀ n < N, ∀ a b, tv (push a (L n)) (push b (L n)) ≤ β*tv a b)
    (he : ∀ n < N, ∀ i, tv (K n i) (L n i) ≤ ε n) :
    (∑ n ∈ Finset.range N, tv (evolve p K n) (evolve p L n)) ≤
      (∑ n ∈ Finset.range N, ε n)/(1-β) := by
  let e := fun n => tv (evolve p K n) (evolve p L n)
  have h0 : e 0=0 := FiniteTV.self p
  have hs := Finset.sum_le_sum (fun n (hn : n ∈ Finset.range N) =>
    discrepancy_step p K L β (ε n) n (hc n (Finset.mem_range.mp hn)) (he n (Finset.mem_range.mp hn)))
  change (∑ n ∈ Finset.range N, e (n+1)) ≤ ∑ n ∈ Finset.range N, (β*e n+ε n) at hs
  rw [Finset.sum_add_distrib,← Finset.mul_sum] at hs
  have htel : (∑ n ∈ Finset.range N, e (n+1))+e 0=(∑ n ∈ Finset.range N, e n)+e N := by
    clear hc he hs
    induction N with
    | zero => simp
    | succ N ih => simp only [Finset.sum_range_succ]; linarith
  have hN : 0 ≤ e N := FiniteTV.nonneg _ _
  apply (le_div_iff₀ (sub_pos.mpr hb)).mpr
  change (∑ n ∈ Finset.range N, e n)*(1-β) ≤ _
  nlinarith

theorem state_loss_gap (p q : FiniteController.Dist I) (f g : I → ℝ) (ξ : ℝ)
    (hg0 : ∀ i, 0 ≤ g i) (hg1 : ∀ i, g i ≤ 1)
    (hfg : ∀ i, f i-g i ≤ ξ) :
    DRGPR.mean p.val f-DRGPR.mean q.val g ≤ ξ+tv p q := by
  have hfg' := DRGPR.mean_mono p.val (fun i => f i-g i) (fun _ => ξ) p.nonneg hfg
  rw [DRGPR.mean_sub,DRGPR.mean_const p.val p.sum_one] at hfg'
  have ht := le_trans (le_abs_self (DRGPR.mean p.val g-DRGPR.mean q.val g))
    (test_bound p q g hg0 hg1)
  linarith

/-- Actual recursively generated state marginals imply the representation ledger. -/
theorem dynamics_loss_ledger (p : FiniteController.Dist I)
    (K L : ℕ → I → FiniteController.Dist I) (β : ℝ) (ε ξ : ℕ → ℝ)
    (f g : ℕ → I → ℝ) (N : ℕ) (hb : β < 1)
    (hc : ∀ n < N, ∀ a b, tv (push a (L n)) (push b (L n)) ≤ β*tv a b)
    (he : ∀ n < N, ∀ i, tv (K n i) (L n i) ≤ ε n)
    (hg0 : ∀ n < N, ∀ i, 0 ≤ g n i) (hg1 : ∀ n < N, ∀ i, g n i ≤ 1)
    (hfg : ∀ n < N, ∀ i, f n i-g n i ≤ ξ n) :
    (∑ n ∈ Finset.range N, (DRGPR.mean (evolve p K n).val (f n)-
      DRGPR.mean (evolve p L n).val (g n))) ≤
      (∑ n ∈ Finset.range N, ξ n)+(∑ n ∈ Finset.range N, ε n)/(1-β) := by
  have hsum := Finset.sum_le_sum (fun n (hn : n ∈ Finset.range N) =>
    state_loss_gap (evolve p K n) (evolve p L n) (f n) (g n) (ξ n)
      (hg0 n (Finset.mem_range.mp hn)) (hg1 n (Finset.mem_range.mp hn)) (hfg n (Finset.mem_range.mp hn)))
  rw [Finset.sum_add_distrib] at hsum
  have h := discrepancy_sum p K L β ε N hb hc he
  linarith

end DRGPR.FiniteDynamics
#print axioms DRGPR.FiniteDynamics.markov_nonexpansive
#print axioms DRGPR.FiniteDynamics.blend_tv
#print axioms DRGPR.FiniteDynamics.push_blend
#print axioms DRGPR.FiniteDynamics.doeblin_contraction
#print axioms DRGPR.FiniteDynamics.discrepancy_step
#print axioms DRGPR.FiniteDynamics.discrepancy_sum
#print axioms DRGPR.FiniteDynamics.state_loss_gap
#print axioms DRGPR.FiniteDynamics.dynamics_loss_ledger
