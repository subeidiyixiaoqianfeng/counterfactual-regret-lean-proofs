import FeedbackLocalOnly

/-! State-dependent local errors for genuinely adaptive reflection schedules.
The charge is averaged on the native path law, not a deterministic union of
all times at which some counterfactual history might reflect. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace DRGPR.StateFeedbackStability
open LocalFeedbackStability FeedbackTrajectory
variable {I : ℕ → Type} [∀ t, Fintype (I t)]

structure Contract (K L : Dynamics I) (c : (t : ℕ) → I t → ℝ) (T : ℕ) where
  epsilon : (t : ℕ) → I t → ℝ
  influence : (t : ℕ) → I t → ℝ
  epsilon_nonneg : ∀ t s, 0 ≤ epsilon t s
  influence_nonneg : ∀ t s, 0 ≤ influence t s
  local_tv : ∀ t, t < T → ∀ s, FiniteTV.tv (K t s) (L t s) ≤ epsilon t s
  lower : (t n : ℕ) → I t → ℝ
  continuation : ∀ t n, t+n+1 ≤ T → ∀ s, epsilon t s ≠ 0 →
    ∀ j, lower t n s ≤ value L c (t+1) n j ∧
      value L c (t+1) n j ≤ lower t n s + influence t s

def Contract.cost {K L : Dynamics I} {c : (t : ℕ) → I t → ℝ} {T : ℕ}
    (C : Contract K L c T) (t : ℕ) (s : I t) :=
  C.influence t s*C.epsilon t s

theorem zero_tv_mean {J : Type} [Fintype J]
    (p q : FiniteController.Dist J) (f : J → ℝ) (h : FiniteTV.tv p q = 0) :
    DRGPR.mean p.val f = DRGPR.mean q.val f := by
  have he : p.val = q.val := by
    funext j
    have hs : (∑ j, |p.val j-q.val j|) = 0 := by
      unfold FiniteTV.tv at h
      linarith
    have hx := Finset.single_le_sum (fun k _ => abs_nonneg (p.val k-q.val k)) (Finset.mem_univ j)
    rw [hs] at hx
    exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hx (abs_nonneg _)))
  rw [he]

theorem value_difference (K L : Dynamics I) (c : (t : ℕ) → I t → ℝ)
    (T : ℕ) (C : Contract K L c T) :
    ∀ t n, t+n ≤ T → ∀ s,
      |value K c t n s-value L c t n s| ≤ value K C.cost t n s := by
  intro t n
  induction n generalizing t with
  | zero => intro _ s; simp [value]
  | succ n ih =>
    intro ht s
    let u := value K c (t+1) n
    let v := value L c (t+1) n
    have hp : |DRGPR.mean (K t s).val u-DRGPR.mean (K t s).val v| ≤
        DRGPR.mean (K t s).val (value K C.cost (t+1) n) := by
      rw [← DRGPR.mean_sub]
      calc
        _ ≤ ∑ j, |(K t s).val j*(u j-v j)| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ j, (K t s).val j*|u j-v j| := by
          simp_rw [abs_mul,abs_of_nonneg ((K t s).nonneg _)]
        _ ≤ _ := Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left
          (ih (t+1) (by omega) j) ((K t s).nonneg j))
    have hl : |DRGPR.mean (K t s).val v-DRGPR.mean (L t s).val v| ≤ C.cost t s := by
      by_cases he : C.epsilon t s = 0
      · have hz : FiniteTV.tv (K t s) (L t s) = 0 :=
          le_antisymm (by simpa [he] using C.local_tv t (by omega) s) (FiniteTV.nonneg _ _)
        rw [zero_tv_mean (K t s) (L t s) v hz]
        simp [Contract.cost,he]
      · exact (span_test (K t s) (L t s) v (C.lower t n s) (C.influence t s)
          (C.influence_nonneg t s) (C.continuation t n (by omega) s he)).trans
          (mul_le_mul_of_nonneg_left (C.local_tv t (by omega) s) (C.influence_nonneg t s))
    have htri := abs_sub_le (DRGPR.mean (K t s).val u)
      (DRGPR.mean (K t s).val v) (DRGPR.mean (L t s).val v)
    change |(c t s+DRGPR.mean (K t s).val u)-
      (c t s+DRGPR.mean (L t s).val v)| ≤
        C.cost t s+DRGPR.mean (K t s).val (value K C.cost (t+1) n)
    rw [add_sub_add_left_eq_sub]
    linarith

theorem actual_loss (K L : Dynamics I) (c : (t : ℕ) → I t → ℝ)
    (p : FiniteController.Dist (I 0)) (T : ℕ) (C : Contract K L c T) :
    |expected K c p T-expected L c p T| ≤ expected K C.cost p T := by
  rw [expected_eq_value,expected_eq_value,expected_eq_value,← DRGPR.mean_sub]
  calc
    _ ≤ ∑ s, |p.val s*(value K c 0 T s-value L c 0 T s)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ s, p.val s*|value K c 0 T s-value L c 0 T s| := by
      simp_rw [abs_mul,abs_of_nonneg (p.nonneg _)]
    _ ≤ _ := Finset.sum_le_sum (fun s _ => mul_le_mul_of_nonneg_left
      (value_difference K L c T C 0 T (by omega) s) (p.nonneg s))

theorem value_mono (K : Dynamics I) (f g : (t : ℕ) → I t → ℝ)
    (h : ∀ t s, f t s ≤ g t s) : ∀ t n s, value K f t n s ≤ value K g t n s := by
  intro t n
  induction n generalizing t with
  | zero => intro s; exact le_rfl
  | succ n ih =>
    intro s
    exact add_le_add (h t s)
      (DRGPR.mean_mono _ _ _ (K t s).nonneg (ih (t+1)))

theorem value_scale (K : Dynamics I) (a : ℝ) (f : (t : ℕ) → I t → ℝ) :
    ∀ t n s, value K (fun r j => a*f r j) t n s = a*value K f t n s := by
  intro t n
  induction n generalizing t with
  | zero => intro s; simp [value]
  | succ n ih =>
    intro s
    simp only [value,ih,DRGPR.mean,mul_add,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    ring

theorem expected_scale (K : Dynamics I) (a : ℝ) (f : (t : ℕ) → I t → ℝ)
    (p : FiniteController.Dist (I 0)) (T : ℕ) :
    expected K (fun r j => a*f r j) p T = a*expected K f p T := by
  simp only [expected_eq_value,value_scale,DRGPR.mean,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  ring

theorem hard_path_expectation (K : Dynamics I) (cost : (t : ℕ) → I t → ℝ)
    (p : FiniteController.Dist (I 0)) (T : ℕ) (B : ℝ)
    (hb : ∀ s h, 0 < p.val s*weight K 0 T s h → loss cost 0 T s h ≤ B) :
    expected K cost p T ≤ B := by
  unfold expected
  have hs (s : I 0) :
      p.val s*(∑ h, weight K 0 T s h*loss cost 0 T s h) ≤ p.val s*B := by
    rw [Finset.mul_sum]
    calc
      _ ≤ ∑ h, p.val s*(weight K 0 T s h*B) := by
        apply Finset.sum_le_sum
        intro h _
        have hn := mul_nonneg (p.nonneg s) (FeedbackTrajectory.nonneg K 0 T s h)
        by_cases hp : 0 < p.val s*weight K 0 T s h
        · simpa only [← mul_assoc] using mul_le_mul_of_nonneg_left (hb s h hp) hn
        · have hz : p.val s*weight K 0 T s h = 0 := le_antisymm (le_of_not_gt hp) hn
          simp only [← mul_assoc,hz,zero_mul,le_refl]
      _ = _ := by rw [← Finset.mul_sum,← Finset.sum_mul,normalized,one_mul]
  calc
    _ ≤ ∑ s, p.val s*B := Finset.sum_le_sum (fun s _ => hs s)
    _ = _ := by rw [← Finset.sum_mul,p.sum_one,one_mul]

theorem adaptive_resource_loss (K L : Dynamics I) (c : (t : ℕ) → I t → ℝ)
    (p : FiniteController.Dist (I 0)) (T : ℕ) (C : Contract K L c T)
    (activity cost : (t : ℕ) → I t → ℝ)
    (H eps cmin B : ℝ) (hH : 0 ≤ H) (heps : 0 ≤ eps) (hcmin : 0 < cmin)
    (hi : ∀ t s, C.influence t s ≤ H)
    (he : ∀ t s, C.epsilon t s ≤ eps*activity t s)
    (hcost : ∀ t s, cmin*activity t s ≤ cost t s)
    (hb : ∀ s h, 0 < p.val s*weight K 0 T s h → loss cost 0 T s h ≤ B) :
    |expected K c p T-expected L c p T| ≤ H*eps*B/cmin := by
  have hw : ∀ t s, C.cost t s ≤ (H*eps/cmin)*cost t s := by
    intro t s
    have ha : activity t s ≤ cost t s/cmin :=
      (le_div_iff₀ hcmin).mpr (by nlinarith [hcost t s])
    calc
      C.cost t s ≤ H*C.epsilon t s :=
        mul_le_mul_of_nonneg_right (hi t s) (C.epsilon_nonneg t s)
      _ ≤ H*(eps*activity t s) := mul_le_mul_of_nonneg_left (he t s) hH
      _ = (H*eps)*activity t s := by ring
      _ ≤ (H*eps)*(cost t s/cmin) :=
        mul_le_mul_of_nonneg_left ha (mul_nonneg hH heps)
      _ = _ := by ring
  have hm : expected K C.cost p T ≤ expected K (fun t s => (H*eps/cmin)*cost t s) p T := by
    rw [expected_eq_value,expected_eq_value]
    exact DRGPR.mean_mono _ _ _ p.nonneg (value_mono K _ _ hw 0 T)
  rw [expected_scale] at hm
  have hbudget := hard_path_expectation K cost p T B hb
  have hmult := mul_le_mul_of_nonneg_left hbudget (div_nonneg (mul_nonneg hH heps) hcmin.le)
  have hgap := actual_loss K L c p T C
  calc
    _ ≤ expected K C.cost p T := hgap
    _ ≤ (H*eps/cmin)*expected K cost p T := hm
    _ ≤ (H*eps/cmin)*B := hmult
    _ = _ := by ring

theorem repaired_counterfactual
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {J : Ω → ℕ → Type*} [∀ ω r, Fintype (J ω r)]
    {M : Type*} [Nonempty M]
    (KA LA : Dynamics I) (KC LC : M → Dynamics I)
    (c : (t : ℕ) → I t → ℝ) (p : FiniteController.Dist (I 0)) (T : ℕ)
    (CA : Contract KA LA c T) (CC : ∀ m, Contract (KC m) (LC m) c T)
    (E : M → DependentTransfer.Experiment Ω J μ) (B : ModelMain.Budget)
    (W : ∀ m, ModelMain.Certificates (E m) B) (η code EA EC : ℝ)
    (hη : ∀ m, (E m).η = η) (hcode : ∀ m, (E m).C = code)
    (hA : ∀ m, (∫ ω, (W m).realA ω ∂μ) = expected LA c p T)
    (hC : ∀ m, (∫ ω, (W m).realM ω ∂μ) = expected (LC m) c p T)
    (hEA : expected KA CA.cost p T ≤ EA)
    (hEC : ∀ m, expected (KC m) (CC m).cost p T ≤ EC) :
    expected KA c p T - sInf (Set.range (fun m => expected (KC m) c p T)) ≤
      B.bound η code + EA + EC := by
  apply DRGPR.infimum_transfer
  · exact Set.range_nonempty _
  · intro x hx
    obtain ⟨m,rfl⟩ := hx
    have hmain := ModelMain.main_fixed (E m) B (W m)
    rw [hA m,hC m,hη m,hcode m] at hmain
    have ha := (abs_le.mp (actual_loss KA LA c p T CA)).2
    have hc := (abs_le.mp (actual_loss (KC m) (LC m) c p T (CC m))).1
    linarith [hEC m]

end DRGPR.StateFeedbackStability
#print axioms DRGPR.StateFeedbackStability.zero_tv_mean
#print axioms DRGPR.StateFeedbackStability.value_difference
#print axioms DRGPR.StateFeedbackStability.actual_loss
#print axioms DRGPR.StateFeedbackStability.value_mono
#print axioms DRGPR.StateFeedbackStability.value_scale
#print axioms DRGPR.StateFeedbackStability.expected_scale
#print axioms DRGPR.StateFeedbackStability.hard_path_expectation
#print axioms DRGPR.StateFeedbackStability.adaptive_resource_loss
#print axioms DRGPR.StateFeedbackStability.repaired_counterfactual
