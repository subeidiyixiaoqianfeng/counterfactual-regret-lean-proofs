import BlockFactorization
import ObliviousMinimax

/- Independent hidden targets and complete block tables are sampled before
play. A master learner sees only erased selected-coordinate transcripts.
Its within-block algorithm can depend on every earlier visible block. -/
noncomputable section
open scoped BigOperators
namespace DRGPR.MultiphaseOblivious
open SupportedInformation FiniteSimulation ObliviousFactorization
open ObliviousInformation TableDistribution
variable {I : Type} [Fintype I] [DecidableEq I]

abbrev Table (I : Type) (n : ℕ) := Hist (I → Bool) n
abbrev Coins (I : Type) (n : ℕ) := Hist (I × Bool) n
abbrev Transcript (I : Type) (n : ℕ) := Hist (I × Option Bool) n
abbrev Environment (I : Type) (n : ℕ) := I × Table I n
abbrev Block (I : Type) (n : ℕ) := Environment I n × Coins I n

structure Master (I : Type) [Fintype I] (n : ℕ) where
  policy : (r : ℕ) → Hist (Transcript I n) r → ObliviousMinimax.Algorithm I

def visibleBlock (n : ℕ) (x : Block I n) : Transcript I n :=
  project visible n (zip n x.1.2 x.2)

def env (q : ℝ) (n : ℕ) (e : Environment I n) : ℝ :=
  (1/(Fintype.card I:ℝ))*pathLaw
    (fun _ _ => row (params (InformationRate.gap (Fintype.card I) q n) e.1)) n e.2

def response (A : Master I n) (q : ℝ)
    (r : ℕ) (e : Hist (Environment I n) r) (a : Hist (Coins I n) r)
    (next : Environment I n) (coins : Coins I n) : ℝ :=
  playerWeight (choice (A.policy r (project (visibleBlock n) r (zip r e a))).p q) n next.2 coins

def joint (A : Master I n) (q : ℝ) := BlockFactorization.kernel (fun _ _ => env q n) (response A q)

def blockRegret (n : ℕ) (x : Block I n) : ℝ :=
  ObliviousMinimax.learnerTotal n (zip n x.1.2 x.2)-ObliviousMinimax.tableTotal x.1.1 n x.1.2

def totalRegret (n : ℕ) := cumulative (fun (_r : ℕ) (_h : Hist (Block I n) _r) x => blockRegret n x)

def fixedGap (A : Master I n) (q : ℝ) (m : ℕ) (e : Hist (Environment I n) m) : ℝ :=
  ∑ a, BlockFactorization.weight (response A q) m e a*totalRegret n m (zip m e a)

theorem env_normalized (q : ℝ) (n : ℕ) (hK : (0:ℝ) < Fintype.card I) :
    ∑ e, env (I:=I) q n e=1 := by
  unfold env
  rw [Fintype.sum_prod_type]
  simp only [← Finset.mul_sum,pathLaw_normalized _ (fun _ _ => row_normalized _),mul_one]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  field_simp

theorem env_nonneg (q : ℝ) (n : ℕ) (hn : 0 < n)
    (hK : (0:ℝ) < Fintype.card I) (hq : 0 < q) (e : Environment I n) :
    0 ≤ env q n e := by
  have he := InformationRate.gap_properties (Fintype.card I) q n hK hq (Nat.cast_pos.mpr hn)
  apply mul_nonneg (by positivity)
  apply pathLaw_nonneg
  intro t h
  apply row_nonneg
  · intro i; unfold params; split_ifs <;> linarith [he.1,he.2.1]
  · intro i; unfold params; split_ifs <;> linarith [he.1,he.2.1]

theorem response_normalized (A : Master I n) (q : ℝ) :
    ∀ r e a next, ∑ coins, response A q r e a next coins=1 := by
  intro r e a next
  exact fixed_player_normalized _ (A.policy r (project (visibleBlock n) r (zip r e a))).normalized q n next.2

theorem response_nonneg (A : Master I n) (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    ∀ r e a next coins, 0 ≤ response A q r e a next coins := by
  intro r e a next coins
  exact ObliviousMinimax.player_nonneg _ q hq hq1 n next.2 coins

theorem one_phase_average (A : ObliviousMinimax.Algorithm I) (q : ℝ) (n : ℕ)
    (hn : 0 < n) (j₀ : I) (hK : (2:ℝ) ≤ Fintype.card I) (hq : 0 < q) (hq1 : q ≤ 1) :
    (1/32:ℝ)*min (n:ℝ) (Real.sqrt ((Fintype.card I)*n/q)) ≤
      ∑ e : Environment I n, env q n e*fixedRegret A.p q e.1 n e.2 := by
  let gap := InformationRate.gap (Fintype.card I) q n
  let L := fun j => ∑ h, pathLaw (ObliviousInformation.kernel A.p q gap j) n h*
    cumulative (fun _ _ x => regretStep j x) n h
  have hK0 : (0:ℝ) < Fintype.card I := by linarith
  have hm : (∑ j, (1/(Fintype.card I:ℝ))*L j) =
      gap*((n:ℝ)-(∑ j, ∑ h, pathLaw
        (fun t h => ErasedBandit.joint (A.p t h) q gap j) n h*ErasedBandit.counts j n h)/
          (Fintype.card I:ℝ)) := by
    simp only [L,expected_regret A.p A.normalized,mul_sub,Finset.sum_sub_distrib]
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    rw [← Finset.mul_sum,← Finset.mul_sum]
    field_simp [hK0.ne']
    <;> ring
  have hbase := FiniteBanditLower.single_phase A.p A.nonneg A.normalized q n hn j₀ hK hq hq1
  dsimp only at hbase
  have he : (∑ e : Environment I n, env q n e*fixedRegret A.p q e.1 n e.2)=
      ∑ j, (1/(Fintype.card I:ℝ))*L j := by
    unfold env
    rw [Fintype.sum_prod_type]
    simp_rw [mul_assoc,← Finset.mul_sum,← fixed_table_factorization]
    rfl
  rw [he,hm]
  exact hbase

theorem conditional_block_lower (A : Master I n) (q : ℝ)
    (hn : 0 < n) (j₀ : I) (hK : (2:ℝ) ≤ Fintype.card I) (hq : 0 < q) (hq1 : q ≤ 1)
    (r : ℕ) (h : Hist (Block I n) r) :
    (1/32:ℝ)*min (n:ℝ) (Real.sqrt ((Fintype.card I)*n/q)) ≤
      ∑ x, joint A q r h x*blockRegret n x := by
  have he : (∑ x, joint A q r h x*blockRegret n x)=
      ∑ e : Environment I n, env q n e*
        fixedRegret (A.policy r (project (visibleBlock n) r h)).p q e.1 n e.2 := by
    unfold joint BlockFactorization.kernel response blockRegret
    rw [Fintype.sum_prod_type]
    simp only [zip_project]
    apply Finset.sum_congr rfl
    intro e _
    unfold fixedRegret
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro coins _
    rw [ObliviousMinimax.gap_identity]
    ring
  rw [he]
  exact one_phase_average _ q n hn j₀ hK hq hq1

theorem joint_normalized (A : Master I n) (q : ℝ) (hK : (0:ℝ) < Fintype.card I) :
    ∀ r h, ∑ x, joint A q r h x=1 :=
  BlockFactorization.kernel_normalized _ _ (fun _ _ => env_normalized q n hK) (response_normalized A q)

theorem joint_nonneg (A : Master I n) (q : ℝ) (hn : 0 < n)
    (hK : (0:ℝ) < Fintype.card I) (hq : 0 < q) (hq1 : q ≤ 1) :
    ∀ r h x, 0 ≤ joint A q r h x := by
  intro r h x
  exact mul_nonneg (env_nonneg q n hn hK hq x.1)
    (response_nonneg A q hq.le hq1 _ _ _ _ _)

theorem multiphase_average (A : Master I n) (q : ℝ) (m : ℕ)
    (hn : 0 < n) (j₀ : I) (hK : (2:ℝ) ≤ Fintype.card I) (hq : 0 < q) (hq1 : q ≤ 1) :
    (m:ℝ)*((1/32:ℝ)*min (n:ℝ) (Real.sqrt ((Fintype.card I)*n/q))) ≤
      ∑ h, pathLaw (joint A q) m h*totalRegret n m h := by
  have hK0 : (0:ℝ) < Fintype.card I := by linarith
  have hk := joint_nonneg A q hn hK0 hq hq1
  have hks := joint_normalized A q hK0
  unfold totalRegret
  rw [expected_cumulative _ _ hks]
  calc
    _ = ∑ r ∈ Finset.range m, ((1/32:ℝ)*min (n:ℝ) (Real.sqrt ((Fintype.card I)*n/q))) := by simp
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro r _
      calc
        _ = (∑ h, pathLaw (joint A q) r h)*
            ((1/32:ℝ)*min (n:ℝ) (Real.sqrt ((Fintype.card I)*n/q))) := by
              rw [pathLaw_normalized _ hks]; ring
        _ ≤ _ := by
          rw [Finset.sum_mul]
          apply Finset.sum_le_sum
          intro h _
          exact mul_le_mul_of_nonneg_left (conditional_block_lower A q hn j₀ hK hq hq1 r h)
            (pathLaw_nonneg _ hk r h)

theorem fixed_table_average (A : Master I n) (q : ℝ) (m : ℕ) :
    (∑ h, pathLaw (joint A q) m h*totalRegret n m h)=
      ∑ e, pathLaw (fun _ _ => env q n) m e*fixedGap A q m e := by
  exact BlockFactorization.expectation_factorization _ _ m _

/-- The entire sequence of targets and tables is fixed independently of the
realized private and logger coins, not chosen after each observed phase. -/
theorem exists_fixed_multiphase_table (A : Master I n) (q : ℝ) (m : ℕ)
    (hn : 0 < n) (j₀ : I) (hK : (2:ℝ) ≤ Fintype.card I) (hq : 0 < q) (hq1 : q ≤ 1) :
    ∃ e : Hist (Environment I n) m,
      (m:ℝ)*((1/32:ℝ)*min (n:ℝ) (Real.sqrt ((Fintype.card I)*n/q))) ≤ fixedGap A q m e := by
  have hK0 : (0:ℝ) < Fintype.card I := by linarith
  letI : Nonempty (Hist (Environment I n) m) :=
    ⟨constantHistory (j₀,constantHistory (fun _ : I => false) n) m⟩
  have h := multiphase_average A q m hn j₀ hK hq hq1
  rw [fixed_table_average] at h
  exact fixed_instance_from_average _ _
    (pathLaw_nonneg _ (fun _ _ => env_nonneg q n hn hK0 hq) m)
    (pathLaw_normalized _ (fun _ _ => env_normalized q n hK0) m) _ h

end DRGPR.MultiphaseOblivious
#print axioms DRGPR.MultiphaseOblivious.env_normalized
#print axioms DRGPR.MultiphaseOblivious.env_nonneg
#print axioms DRGPR.MultiphaseOblivious.response_normalized
#print axioms DRGPR.MultiphaseOblivious.response_nonneg
#print axioms DRGPR.MultiphaseOblivious.one_phase_average
#print axioms DRGPR.MultiphaseOblivious.conditional_block_lower
#print axioms DRGPR.MultiphaseOblivious.joint_normalized
#print axioms DRGPR.MultiphaseOblivious.joint_nonneg
#print axioms DRGPR.MultiphaseOblivious.multiphase_average
#print axioms DRGPR.MultiphaseOblivious.fixed_table_average
#print axioms DRGPR.MultiphaseOblivious.exists_fixed_multiphase_table
