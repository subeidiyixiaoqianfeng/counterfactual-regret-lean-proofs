import PrimitiveTailRegret

noncomputable section
open scoped BigOperators
namespace DRGPR.PrimitiveUniversalPhase
open SupportedInformation HistoryAppend BlockFlattening BlockMacroEncoding
open PrimitiveTaskRegret PrimitiveTailRegret
variable {I : Type} [Fintype I] [DecidableEq I]

theorem tables_congr (d : ℕ) (e f : ℕ → Hist (I → Bool) (d+1)) :
    ∀ r, (∀ k < r, e k=f k) → tables d e r=tables d f r := by
  intro r
  induction r with
  | zero => intro h; rfl
  | succ r ih =>
    intro h
    change (tables d e r,e r)=(tables d f r,f r)
    exact Prod.ext (ih (fun k hk => h k (by omega))) (h r (by omega))

theorem tables_surjective (d : ℕ) :
    ∀ r (h : Hist (Hist (I → Bool) (d+1)) r), ∃ e, tables d e r=h := by
  intro r
  induction r with
  | zero =>
    intro h
    cases h
    exact ⟨fun _ => HistoryFunction.ofFn (d+1) (fun _ _ => true),rfl⟩
  | succ r ih =>
    intro h
    obtain ⟨e,he⟩ := ih h.1
    let f := fun k => if k=r then h.2 else e k
    refine ⟨f,?_⟩
    change (tables d f r,f r)=h
    have hf : tables d f r=tables d e r := tables_congr d f e r (fun k hk => by simp [f,show k≠r by omega])
    rw [hf,he]
    simp only [f,if_true]
    rfl

/-- Every fixed primitive table has the required complete-run/tail encoding.
No special table family or loss-free padding is assumed. -/
theorem table_decomposition (d r s : ℕ)
    (table : Hist (I → Bool) (length (d+1) r+(s+1))) :
    ∃ e tail, table=append (length (d+1) r) (flatten (d+1) r (tables d e r)) (s+1) tail := by
  obtain ⟨e,he⟩ := tables_surjective d r
    (unflatten (d+1) r (take (length (d+1) r) (s+1) table))
  refine ⟨e,drop (length (d+1) r) (s+1) table,?_⟩
  rw [he,flatten_unflatten,append_split]

def bound (n b : ℕ) (K q η a : ℝ) : ℝ :=
  (a/η+η/2*(K*((b:ℝ)+1/q)*n)+(n:ℝ)/b+b+1)/2

theorem universal_phase_bound (label : I → ℕ) (n b : ℕ) (hn : 0 < n) (hb : 0 < b)
    (table : Hist (I → Bool) n) (q η : ℝ) (hq : 0 < q) (hq1 : q ≤ 1) (hη : 0 < η)
    (p : FiniteController.Dist I) (hp : ∀ i, 0 < p.val i) (f j : I) :
    (∑ a, ObliviousFactorization.playerWeight
      (ObliviousInformation.choice (PrimitiveRun.algorithm q η b p f).p q) n table a *
      taskTotal label n table a)-ObliviousMinimax.tableTotal j n table/2 ≤
      bound n b (Fintype.card I) q η (-Real.log (p.val j)) := by
  obtain ⟨d,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hb)
  let r := (n-1)/(d+1)
  let s := (n-1)%(d+1)
  have hdecomp := PhaseFlattening.horizon_decomposition n (d+1) hn (by omega)
  change length (d+1) r+(s+1)=n ∧ s+1 ≤ d+1 at hdecomp
  obtain ⟨hlen,hs⟩ := hdecomp
  have hrn : (r:ℝ)*(d+1:ℕ) ≤ (n:ℝ) := by
    have he : r*(d+1) ≤ n := by rw [length_eq,Nat.mul_comm (d+1) r] at hlen; omega
    exact_mod_cast he
  have hrd : (r:ℝ) ≤ (n:ℝ)/(d+1:ℕ) := (le_div_iff₀ (by positivity)).mpr hrn
  have hvar : (r:ℝ)*(Fintype.card I:ℝ)*(((d+1:ℕ):ℝ)^2+(d+1:ℕ)/q) ≤
      (Fintype.card I:ℝ)*((d+1:ℕ)+1/q)*n := by
    have hh := mul_le_mul_of_nonneg_left hrn
      (show 0 ≤ (Fintype.card I:ℝ)*((d+1:ℕ)+1/q) by positivity)
    convert hh using 1 <;> ring
  have he (table : Hist (I → Bool) (length (d+1) r+(s+1))) := table_decomposition d r s table
  have ht : ∀ table : Hist (I → Bool) (length (d+1) r+(s+1)),
      (∑ a, ObliviousFactorization.playerWeight
        (ObliviousInformation.choice (PrimitiveRun.algorithm q η (d+1) p f).p q)
        (length (d+1) r+(s+1)) table a * taskTotal label (length (d+1) r+(s+1)) table a)-
        ObliviousMinimax.tableTotal j (length (d+1) r+(s+1)) table/2 ≤
      bound n (d+1) (Fintype.card I) q η (-Real.log (p.val j)) := by
    intro table
    obtain ⟨e,tail,rfl⟩ := he table
    have ht := primitive_arbitrary_horizon label d r s hs e tail q η hq hq1 hη p hp f j
    have hsr : ((s+1:ℕ):ℝ) ≤ (d+1:ℕ) := Nat.cast_le.mpr hs
    have hv := mul_le_mul_of_nonneg_left hvar (show 0 ≤ η/2 by positivity)
    unfold bound
    linarith
  rw [hlen] at ht
  exact ht table

end DRGPR.PrimitiveUniversalPhase
#print axioms DRGPR.PrimitiveUniversalPhase.tables_congr
#print axioms DRGPR.PrimitiveUniversalPhase.tables_surjective
#print axioms DRGPR.PrimitiveUniversalPhase.table_decomposition
#print axioms DRGPR.PrimitiveUniversalPhase.universal_phase_bound
