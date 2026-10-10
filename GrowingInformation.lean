import DependentFactorization
import MultiphaseOblivious

noncomputable section
open scoped BigOperators
namespace DRGPR.GrowingInformation
open DependentBlocks
open MultiphaseOblivious (Table Coins Transcript Environment Block)
open ObliviousInformation
variable {K : ℕ → ℕ} {n : ℕ}

/-- A causal learner whose available identity type can differ at every phase.
Only earlier visible phase transcripts enter the policy constructor. -/
structure Master (K : ℕ → ℕ) (n : ℕ) where
  policy : (r : ℕ) → History (fun s => Transcript (Fin (K s)) n) r →
    ObliviousMinimax.Algorithm (Fin (K r))

def visible (r : ℕ) (x : Block (Fin (K r)) n) : Transcript (Fin (K r)) n :=
  MultiphaseOblivious.visibleBlock n x

def response (A : Master K n) (q : ℝ) (r : ℕ)
    (e : History (fun s => Environment (Fin (K s)) n) r)
    (a : History (fun s => Coins (Fin (K s)) n) r)
    (next : Environment (Fin (K r)) n) (coins : Coins (Fin (K r)) n) : ℝ :=
  ObliviousFactorization.playerWeight
    (choice (A.policy r (DependentFactorization.project visible r (DependentFactorization.zip r e a))).p q)
    n next.2 coins

def joint (A : Master K n) (q : ℝ) := DependentFactorization.kernel
  (fun r _ => MultiphaseOblivious.env (I := Fin (K r)) q n) (response A q)

def cost (r : ℕ) (_h : History (fun s => Block (Fin (K s)) n) r)
    (x : Block (Fin (K r)) n) : ℝ := MultiphaseOblivious.blockRegret n x

def lower (K : ℕ → ℕ) (n : ℕ) (q : ℝ) (r : ℕ) : ℝ :=
  (1/32:ℝ)*min (n:ℝ) (Real.sqrt ((K r:ℝ)*n/q))

def fixedGap (A : Master K n) (q : ℝ) (m : ℕ)
    (e : History (fun s => Environment (Fin (K s)) n) m) : ℝ :=
  ∑ a, DependentFactorization.weight (response A q) m e a*
    total cost m (DependentFactorization.zip m e a)

theorem response_normalized (A : Master K n) (q : ℝ) :
    ∀ r e a next, ∑ coins, response A q r e a next coins=1 := by
  intro r e a next
  exact ObliviousInformation.fixed_player_normalized _
    (A.policy r (DependentFactorization.project visible r (DependentFactorization.zip r e a))).normalized q n next.2

theorem response_nonneg (A : Master K n) (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    ∀ r e a next coins, 0 ≤ response A q r e a next coins := by
  intro r e a next coins
  exact ObliviousMinimax.player_nonneg _ q hq hq1 n next.2 coins

theorem joint_normalized (A : Master K n) (q : ℝ) (hK : ∀ r, 2 ≤ K r) :
    ∀ r h, ∑ x, joint A q r h x=1 := by
  apply DependentFactorization.kernel_normalized
  · intro r _
    apply MultiphaseOblivious.env_normalized
    simpa using (show (0:ℝ) < K r by exact_mod_cast (by have := hK r; omega : 0 < K r))
  · exact response_normalized A q

theorem joint_nonneg (A : Master K n) (q : ℝ) (hn : 0 < n)
    (hK : ∀ r, 2 ≤ K r) (hq : 0 < q) (hq1 : q ≤ 1) :
    ∀ r h x, 0 ≤ joint A q r h x := by
  intro r h x
  apply mul_nonneg
  · apply MultiphaseOblivious.env_nonneg q n hn _ hq
    simpa using (show (0:ℝ) < K r by exact_mod_cast (by have := hK r; omega : 0 < K r))
  · exact response_nonneg A q hq.le hq1 _ _ _ _ _

theorem conditional_lower (A : Master K n) (q : ℝ) (hn : 0 < n)
    (hK : ∀ r, 2 ≤ K r) (hq : 0 < q) (hq1 : q ≤ 1)
    (r : ℕ) (h : History (fun s => Block (Fin (K s)) n) r) :
    lower K n q r ≤ ∑ x, joint A q r h x*cost r h x := by
  have he : (∑ x, joint A q r h x*cost r h x)=
      ∑ e : Environment (Fin (K r)) n, MultiphaseOblivious.env q n e*
        fixedRegret (A.policy r (DependentFactorization.project visible r h)).p q e.1 n e.2 := by
    unfold joint DependentFactorization.kernel response cost MultiphaseOblivious.blockRegret
    rw [Fintype.sum_prod_type]
    simp only [DependentFactorization.zip_project]
    apply Finset.sum_congr rfl
    intro e _
    unfold fixedRegret
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro coins _
    rw [ObliviousMinimax.gap_identity]
    ring
  rw [he]
  have hKr : (2:ℝ) ≤ Fintype.card (Fin (K r)) := by simpa using (show (2:ℝ) ≤ K r by exact_mod_cast hK r)
  simpa [lower] using MultiphaseOblivious.one_phase_average
    (A.policy r (DependentFactorization.project visible r h)) q n hn
    (⟨0,by have := hK r; omega⟩ : Fin (K r)) hKr hq hq1

theorem average_lower (A : Master K n) (q : ℝ) (hn : 0 < n)
    (hK : ∀ r, 2 ≤ K r) (hq : 0 < q) (hq1 : q ≤ 1) :
    ∀ m, (∑ r ∈ Finset.range m, lower K n q r) ≤ ∑ h, law (joint A q) m h*total cost m h := by
  intro m
  induction m with
  | zero => simp [History,law,total]
  | succ m ih =>
    rw [expected_step _ _ (joint_normalized A q hK),Finset.sum_range_succ]
    apply add_le_add ih
    calc
      _ = ∑ h, law (joint A q) m h*lower K n q m := by
        rw [← Finset.sum_mul,DependentBlocks.normalized _ (joint_normalized A q hK),one_mul]
      _ ≤ _ := Finset.sum_le_sum (fun h _ => mul_le_mul_of_nonneg_left
        (conditional_lower A q hn hK hq hq1 m h)
        (DependentBlocks.nonneg _ (joint_nonneg A q hn hK hq hq1) m h))

theorem fixed_table_average (A : Master K n) (q : ℝ) (m : ℕ) :
    (∑ h, law (joint A q) m h*total cost m h)=
      ∑ e, law (fun r _ => MultiphaseOblivious.env (I := Fin (K r)) q n) m e*fixedGap A q m e := by
  exact DependentFactorization.expectation_factorization _ _ m _

def defaultEnvironment (hK : ∀ r, 2 ≤ K r) :
    (m : ℕ) → History (fun r => Environment (Fin (K r)) n) m
  | 0 => ()
  | m+1 => (defaultEnvironment hK m,
      (⟨0,by have := hK m; omega⟩,ObliviousInformation.constantHistory (fun _ => false) n))

/-- One entire growing-library table sequence is fixed before private and
logging draws. The environment is not reselected after each phase. -/
theorem exists_fixed_table (A : Master K n) (q : ℝ) (m : ℕ) (hn : 0 < n)
    (hK : ∀ r, 2 ≤ K r) (hq : 0 < q) (hq1 : q ≤ 1) :
    ∃ e : History (fun r => Environment (Fin (K r)) n) m,
      (∑ r ∈ Finset.range m, lower K n q r) ≤ fixedGap A q m e := by
  letI : Nonempty (History (fun r => Environment (Fin (K r)) n) m) := ⟨defaultEnvironment hK m⟩
  have hh := average_lower A q hn hK hq hq1 m
  rw [fixed_table_average] at hh
  apply ObliviousFactorization.fixed_instance_from_average _ _ _ _ _ hh
  · apply DependentBlocks.nonneg
    intro r _ e
    apply MultiphaseOblivious.env_nonneg q n hn _ hq
    simpa using (show (0:ℝ) < K r by exact_mod_cast (by have := hK r; omega : 0 < K r))
  · apply DependentBlocks.normalized
    intro r _
    apply MultiphaseOblivious.env_normalized
    simpa using (show (0:ℝ) < K r by exact_mod_cast (by have := hK r; omega : 0 < K r))

end DRGPR.GrowingInformation
#print axioms DRGPR.GrowingInformation.response_normalized
#print axioms DRGPR.GrowingInformation.response_nonneg
#print axioms DRGPR.GrowingInformation.joint_normalized
#print axioms DRGPR.GrowingInformation.joint_nonneg
#print axioms DRGPR.GrowingInformation.conditional_lower
#print axioms DRGPR.GrowingInformation.average_lower
#print axioms DRGPR.GrowingInformation.fixed_table_average
#print axioms DRGPR.GrowingInformation.exists_fixed_table
