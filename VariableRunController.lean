import GranularObservable

/- Predictable variable-length runs, including empty terminal padding.
The finite mask envelope is a representation device, not a fixed run length.
The total-duration assumption is pathwise and does not assume a regret bound. -/
noncomputable section
open scoped BigOperators
namespace DRGPR.VariableRunController
open FiniteController SupportedInformation GranularObservation
variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

def masked (s : Finset J) (l : I → J → ℝ) (i : I) (t : J) : ℝ :=
  if t ∈ s then l i t else 0

theorem masked_nonneg (s : Finset J) (l : I → J → ℝ)
    (hl : ∀ i t, 0 ≤ l i t) (i : I) (t : J) : 0 ≤ masked s l i t := by
  unfold masked
  split_ifs <;> first | exact hl i t | norm_num

theorem masked_le_one (s : Finset J) (l : I → J → ℝ)
    (hl : ∀ i t, l i t ≤ 1) (i : I) (t : J) : masked s l i t ≤ 1 := by
  unfold masked
  split_ifs <;> first | exact hl i t | norm_num

theorem masked_sum (s : Finset J) (l : I → J → ℝ) (i : I) :
    (∑ t, masked s l i t) = ∑ t ∈ s, l i t := by
  simp [masked]

theorem masked_second_bound (q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1)
    (s : Finset J) (l : I → J → ℝ)
    (hl : ∀ i t, 0 ≤ l i t) (hl1 : ∀ i t, l i t ≤ 1) (i : I) :
    (∑ x, TableDistribution.row (fun _ : J => q) x *
      (score q (masked s l i) x)^2) ≤ (s.card:ℝ)^2+(s.card:ℝ)/q := by
  rw [score_second q hq.ne']
  have hsum0 : 0 ≤ ∑ t, masked s l i t :=
    Finset.sum_nonneg (fun t _ => masked_nonneg s l hl i t)
  have hsum : (∑ t, masked s l i t) ≤ (s.card:ℝ) := by
    rw [masked_sum]
    calc
      _ ≤ ∑ _t ∈ s, (1:ℝ) := Finset.sum_le_sum (fun t _ => hl1 i t)
      _ = _ := by simp
  have hsq : (∑ t, (masked s l i t)^2) ≤ (s.card:ℝ) := by
    have he : (∑ t, (masked s l i t)^2) = ∑ t ∈ s, (l i t)^2 := by
      simp [masked,ite_pow]
    rw [he]
    calc
      _ ≤ ∑ _t ∈ s, (1:ℝ) := Finset.sum_le_sum (fun t _ => by nlinarith [hl i t,hl1 i t])
      _ = _ := by simp
  have hc : 0 ≤ 1/q-1 := by
    have hh : (1:ℝ) ≤ 1/q := (le_div_iff₀ hq).2 (by simpa using hq1)
    linarith
  have hh := DRGPR.square_bounded _ _ hsum0 hsum
  have hm := mul_le_mul_of_nonneg_left hsq hc
  have hn : (0:ℝ) ≤ s.card := Nat.cast_nonneg _
  have he : (1/q-1)*(s.card:ℝ)=(s.card:ℝ)/q-s.card := by ring
  rw [he] at hm
  linarith

theorem masked_weighted_second (q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1)
    (s : Finset J) (l : I → J → ℝ)
    (hl : ∀ i t, 0 ≤ l i t) (hl1 : ∀ i t, l i t ≤ 1)
    (p : FiniteController.Dist I) (hp : ∀ i, 0 < p.val i) :
    let D := (GranularController.feedback q hq hq1 (masked s l)
      (masked_nonneg s l hl) (masked_le_one s l hl1)).round p
    D.avg (fun draw o => ∑ i, p.val i*(D.estimate draw o i)^2) ≤
      (Fintype.card I:ℝ)*((s.card:ℝ)^2+(s.card:ℝ)/q) := by
  dsimp only
  rw [GranularController.exact_second q hq hq1 (masked s l)
    (masked_nonneg s l hl) (masked_le_one s l hl1) p hp]
  calc
    _ ≤ ∑ _i : I, ((s.card:ℝ)^2+(s.card:ℝ)/q) :=
      Finset.sum_le_sum (fun i _ => masked_second_bound q hq hq1 s l hl hl1 i)
    _ = _ := by simp; ring

def duration (s : (n : ℕ) → Hist (I × (J → Bool)) n → Finset J)
    (n : ℕ) (h : Hist (I × (J → Bool)) n) (_a : I × (J → Bool)) : ℝ :=
  (s n h).card

theorem expected_duration (A : Program I (J → Bool))
    (s : (n : ℕ) → Hist (I × (J → Bool)) n → Finset J) (N : ℕ) :
    (∑ h, pathLaw A.kernel N h*cumulative (duration s) N h) =
      ∑ n ∈ Finset.range N, ∑ h, pathLaw A.kernel n h*((s n h).card:ℝ) := by
  rw [expected_cumulative _ _ A.kernel_sum]
  simp only [duration,← Finset.sum_mul,A.kernel_sum,one_mul]

/-- The support is chosen from the past, before the current private draw.
There is no lower bound on duration: an empty tail contributes exactly zero. -/
def algorithm (q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1) (η : ℝ) (hη : 0 < η)
    (initial : FiniteController.Dist I)
    (s : (n : ℕ) → Hist (I × (J → Bool)) n → Finset J)
    (l : (n : ℕ) → Hist (I × (J → Bool)) n → I → J → ℝ)
    (hl : ∀ n h i t, 0 ≤ l n h i t) (hl1 : ∀ n h i t, l n h i t ≤ 1) :
    Program I (J → Bool) :=
  GranularController.algorithm q hq hq1 η hη initial
    (fun n h => masked (s n h) (l n h))
    (fun n h => masked_nonneg (s n h) (l n h) (hl n h))
    (fun n h => masked_le_one (s n h) (l n h) (hl1 n h))

theorem variable_run_regret (q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1)
    (η : ℝ) (hη : 0 < η) (initial : FiniteController.Dist I)
    (hi : ∀ i, 0 < initial.val i)
    (s : (n : ℕ) → Hist (I × (J → Bool)) n → Finset J)
    (l : (n : ℕ) → Hist (I × (J → Bool)) n → I → J → ℝ)
    (hl : ∀ n h i t, 0 ≤ l n h i t) (hl1 : ∀ n h i t, l n h i t ≤ 1)
    (N : ℕ) (j : I) (b T : ℝ) (hb : 0 ≤ b)
    (hs : ∀ n h, ((s n h).card:ℝ) ≤ b)
    (ht : ∀ h, cumulative (duration s) N h ≤ T) :
    let A := algorithm q hq hq1 η hη initial s l hl hl1
    (∑ h, pathLaw A.kernel N h*cumulative (A.actualGap (fun _ _ => j)) N h) ≤
      -Real.log (initial.val j)/η+η/2*((Fintype.card I:ℝ)*(b+1/q)*T) := by
  let A := algorithm q hq hq1 η hη initial s l hl hl1
  have htrans (i : I) : ∀ n (h : Hist (I × (J → Bool)) (n+1)),
      0 < (A.transition n h i).val i := by
    intro n h
    simp [A,algorithm,GranularController.algorithm,identityRows]
  have hactive (n : ℕ) (h : Hist (I × (J → Bool)) n) (i : I) :
      0 < (A.state n h).val i := A.bridge_active (fun _ _ => i) (hi i) (htrans i) n h
  have hzero : ∀ n h, cumulative (A.codeIncrement (fun _ _ => j)) n h = 0 := by
    intro n
    induction n with
    | zero => intro h; rfl
    | succ n ih =>
      intro h
      rw [cumulative,ih]
      simp [Program.codeIncrement,A,algorithm,GranularController.algorithm,
        identityRows]
  have hcode : ∀ h, -Real.log (A.initial.val j)+
      cumulative (A.codeIncrement (fun _ _ => j)) N h ≤ -Real.log (initial.val j) := by
    intro h
    rw [hzero]
    simp [A,algorithm,GranularController.algorithm]
  let c := (Fintype.card I:ℝ)*(b+1/q)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hv (n : ℕ) (h : Hist (I × (J → Bool)) n) :
      (A.round n h).avg (fun i o => DRGPR.mean (A.state n h).val
        (fun k => ((A.round n h).estimate i o k)^2)) ≤ c*((s n h).card:ℝ) := by
    have hh := masked_weighted_second q hq hq1 (s n h) (l n h)
      (hl n h) (hl1 n h) (A.state n h) (hactive n h)
    have hd : (0:ℝ) ≤ (s n h).card := Nat.cast_nonneg _
    have hsq : ((s n h).card:ℝ)^2 ≤ b*((s n h).card:ℝ) := by
      nlinarith [mul_le_mul_of_nonneg_right (hs n h) hd]
    have hk : (0:ℝ) ≤ Fintype.card I := Nat.cast_nonneg _
    have hm := mul_le_mul_of_nonneg_left
      (show ((s n h).card:ℝ)^2+((s n h).card:ℝ)/q ≤
        (b+1/q)*((s n h).card:ℝ) by
          calc
            _ ≤ b*((s n h).card:ℝ)+((s n h).card:ℝ)/q := by linarith
            _ = _ := by ring) hk
    exact hh.trans (by dsimp [c]; nlinarith)
  have hbound := A.regret_local_variance (fun _ _ => j) N (-Real.log (initial.val j))
    (hi j) (htrans j) hcode (fun n h => c*((s n h).card:ℝ)) hv
  have he : (∑ n ∈ Finset.range N, ∑ h,
      pathLaw A.kernel n h*(c*((s n h).card:ℝ))) =
      c*(∑ h, pathLaw A.kernel N h*cumulative (duration s) N h) := by
    rw [expected_duration]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    apply Finset.sum_congr rfl
    intro h _
    ring
  have htmean : (∑ h, pathLaw A.kernel N h*cumulative (duration s) N h) ≤ T := by
    calc
      _ ≤ ∑ h, pathLaw A.kernel N h*T := Finset.sum_le_sum
        (fun h _ => mul_le_mul_of_nonneg_left (ht h) (A.law_nonneg N h))
      _ = T := by rw [← Finset.sum_mul,A.law_normalized,one_mul]
  rw [he] at hbound
  have hm := mul_le_mul_of_nonneg_left htmean hc
  have hh := mul_le_mul_of_nonneg_left hm (by positivity : 0 ≤ η/2)
  change _ ≤ -Real.log (initial.val j)/η+η/2*(c*T)
  change _ ≤ -Real.log (initial.val j)/η+η/2*
    (c*(∑ h, pathLaw A.kernel N h*cumulative (duration s) N h)) at hbound
  linarith

theorem empty_score (q : ℝ) (l : I → J → ℝ) (i : I) (x : J → Bool) :
    score q (masked ∅ l i) x = 0 := by simp [score,masked]

end DRGPR.VariableRunController
#print axioms DRGPR.VariableRunController.masked_nonneg
#print axioms DRGPR.VariableRunController.masked_le_one
#print axioms DRGPR.VariableRunController.masked_sum
#print axioms DRGPR.VariableRunController.masked_second_bound
#print axioms DRGPR.VariableRunController.masked_weighted_second
#print axioms DRGPR.VariableRunController.expected_duration
#print axioms DRGPR.VariableRunController.variable_run_regret
#print axioms DRGPR.VariableRunController.empty_score
