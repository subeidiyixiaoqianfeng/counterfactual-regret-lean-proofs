import LocalNativeFamily

/- Additional correspondence checks for the v17 presentation.
   These wrappers retain the model premises and invoke the existing proofs.
   They do not postulate the desired native regret bound. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology
namespace DRGPR.PaperV17Correspondence

theorem explicit_second_moment
    {Ω : Type*} [MeasurableSpace Ω] {Γ : Measure Ω}
    {I : Ω → ℕ → Type*} [∀ ω r, Fintype (I ω r)]
    (E : DependentTransfer.Experiment Ω I Γ) :
    (∑ r ∈ Finset.range (E.R+1), ∫ ω,
      ∑ i, Growing.prob (E.ν ω) (E.P ω) (E.z ω) E.η r i *
        (E.z ω r i)^2 ∂Γ) ≤ E.V := by
  simpa only [DependentSelection.square, DRGPR.mean] using E.capacity

theorem expected_selection_endpoints
    {Ω : Type*} [MeasurableSpace Ω] {Γ : Measure Ω} [IsProbabilityMeasure Γ]
    {I : Ω → ℕ → Type*} [∀ ω r, Fintype (I ω r)]
    (E : DependentTransfer.Experiment Ω I Γ) :
    E.selectedTotal-E.availableTotal ≤ E.C/E.η+E.η*E.V/2 :=
  E.selection

theorem endpoint_telescope (a ar s v al cl pa mr c : ℝ) :
    a-c = (a-ar)+(ar-s)+(s-v)+(v-al)+(al-cl)+(cl-pa)+(pa-mr)+(mr-c) := by
  ring

theorem exact_budget (B : ModelMain.Budget) (η C : ℝ) :
    B.bound η C =
      B.E_cpA+B.F+B.D_A+B.G+B.D_C+B.E_nf+B.E_cpC+
      C/η+η*B.b*B.V/2+
      (B.H:ℝ)*(Nat.ceil ((B.T:ℝ)/(B.b:ℝ))+B.N+1)+
      (B.b:ℝ)*B.S+(B.H:ℝ)*(B.S+1) := by
  unfold ModelMain.Budget.bound ModelMain.Budget.delta ModelMain.Budget.prefix
  ring

/-- Unlike the earlier packaged family, this wrapper permits finite trial
    alphabets, state domains, and episode sets to vary with the horizon.
    It uses the total resource condition printed in the paper directly. -/
theorem local_family_variable_domains
    {Ω : Type*} [MeasurableSpace Ω] {M : Type*} [Nonempty M]
    (I D : ℕ → Type) [∀ n, Fintype (I n)] [∀ n, Fintype (D n)]
    (X : ℕ → ℕ → Type) [∀ n t, Fintype (X n t)]
    (Γ : ℕ → M → Measure Ω) [∀ n m, IsProbabilityMeasure (Γ n m)]
    (J : ℕ → M → Ω → ℕ → Type*) [∀ n m ω r, Fintype (J n m ω r)]
    (A : (n : ℕ) → LocalNativeFamily.Instance
      (I:=I n) (X:=X n) (D:=D n) (Γ n) (J n))
    (rho κ : ℝ) (attempts : ℕ → ℕ)
    (hr : 0 < rho) (hr1 : rho ≤ 1)
    (he : ∀ n, (A n).failure = (1-rho)^attempts n)
    (hk : ∀ n, (A n).influence*(A n).error/(A n).mincost = κ)
    (hu : Tendsto (fun n => (A n).rest/(A n).horizon) atTop (𝓝 0))
    (hd : Tendsto (fun n => (A n).delay/(A n).horizon) atTop (𝓝 0))
    (hq : Tendsto (fun n => (A n).delta) atTop (𝓝 0))
    (hn : Tendsto attempts atTop atTop)
    (hb : Tendsto (fun n => ((A n).learnerCost+(A n).comparatorCost)/
      (A n).horizon) atTop (𝓝 0)) :
    Tendsto (fun n => max 0 ((A n).regret/(A n).horizon)) atTop (𝓝 0) := by
  have hT (n) : (0:ℝ) < (A n).horizon := Nat.cast_pos.mpr (A n).horizon_pos
  apply NativeNoRegret.upper_no_regret (fun n => (A n).regret)
    (fun n => (A n).rest+(A n).delay+(A n).horizon*((A n).delta+(1-rho)^attempts n)+
      κ*((A n).learnerCost+(A n).comparatorCost))
    (fun n => ((A n).horizon:ℝ)) hT
  · intro n
    simpa only [he n, hk n] using (A n).bound
  · have hp := (tendsto_pow_atTop_nhds_zero_of_lt_one (sub_nonneg.mpr hr1)
      (show 1-rho < 1 by linarith)).comp hn
    have hz := ((hu.add hd).add (hq.add hp)).add (hb.const_mul κ)
    convert hz using 1 <;> try norm_num
    funext n
    dsimp
    field_simp [(hT n).ne']
    <;> ring

end DRGPR.PaperV17Correspondence
#print axioms DRGPR.PaperV17Correspondence.explicit_second_moment
#print axioms DRGPR.PaperV17Correspondence.expected_selection_endpoints
#print axioms DRGPR.PaperV17Correspondence.endpoint_telescope
#print axioms DRGPR.PaperV17Correspondence.exact_budget
#print axioms DRGPR.PaperV17Correspondence.local_family_variable_domains
