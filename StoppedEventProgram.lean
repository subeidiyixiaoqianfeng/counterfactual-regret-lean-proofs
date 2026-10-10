import DependentBlocks

/-! A genuinely generated, bounded stopped event program.
The continuation decision is a function of the completed history. It may
depend on every earlier action, observation, and generation event. It cannot
depend on the event about to be sampled. none is an absorbing terminal token,
not a freshly sampled dummy action. Event alphabets may vary with time. -/
noncomputable section
open scoped BigOperators
namespace DRGPR.StoppedEventProgram
open DependentBlocks
variable {E : ℕ → Type} [∀ n, Fintype (E n)]

def live (go : (n : ℕ) → History (fun t => Option (E t)) n → Bool) :
    (n : ℕ) → History (fun t => Option (E t)) n → Bool
  | 0, h => go 0 h
  | n+1, h => live go n h.1 && h.2.isSome && go (n+1) h

def kernel (go : (n : ℕ) → History (fun t => Option (E t)) n → Bool)
    (k : (n : ℕ) → History (fun t => Option (E t)) n → E n → ℝ)
    (n : ℕ) (h : History (fun t => Option (E t)) n) : Option (E n) → ℝ
  | none => if live go n h then 0 else 1
  | some x => if live go n h then k n h x else 0

def score (f : (n : ℕ) → History (fun t => Option (E t)) n → E n → ℝ)
    (n : ℕ) (h : History (fun t => Option (E t)) n) : Option (E n) → ℝ
  | none => 0
  | some x => f n h x

theorem terminal_absorbs (go : (n : ℕ) → History (fun t => Option (E t)) n → Bool)
    (n : ℕ) (h : History (fun t => Option (E t)) n) :
    live go (n+1) (h, none) = false := by simp [live]

theorem dead_stays_dead (go : (n : ℕ) → History (fun t => Option (E t)) n → Bool)
    (n : ℕ) (h : History (fun t => Option (E t)) n) (x : Option (E n))
    (hd : live go n h = false) : live go (n+1) (h,x) = false := by
  simp [live, hd]

theorem kernel_normalized (go : (n : ℕ) → History (fun t => Option (E t)) n → Bool)
    (k : (n : ℕ) → History (fun t => Option (E t)) n → E n → ℝ)
    (hk : ∀ n h, ∑ x, k n h x = 1) (n : ℕ)
    (h : History (fun t => Option (E t)) n) :
    ∑ x, kernel go k n h x = 1 := by
  rw [Fintype.sum_option]
  cases hl : live go n h <;> simp [kernel, hl, hk]

theorem kernel_nonneg (go : (n : ℕ) → History (fun t => Option (E t)) n → Bool)
    (k : (n : ℕ) → History (fun t => Option (E t)) n → E n → ℝ)
    (hk : ∀ n h x, 0 ≤ k n h x) (n : ℕ)
    (h : History (fun t => Option (E t)) n) (x : Option (E n)) :
    0 ≤ kernel go k n h x := by
  cases x <;> cases hl : live go n h <;> simp [kernel, hl, hk]

theorem local_moment (go : (n : ℕ) → History (fun t => Option (E t)) n → Bool)
    (k f : (n : ℕ) → History (fun t => Option (E t)) n → E n → ℝ)
    (n : ℕ) (h : History (fun t => Option (E t)) n) :
    (∑ x, kernel go k n h x * score f n h x) =
      if live go n h then ∑ x, k n h x * f n h x else 0 := by
  rw [Fintype.sum_option]
  cases hl : live go n h <;> simp [kernel, score, hl]

/-- No stopped-expectation identity is a premise. It is derived from the
recursively generated law and the one-event moments at live histories. -/
theorem stopped_zero_moment
    (go : (n : ℕ) → History (fun t => Option (E t)) n → Bool)
    (k f : (n : ℕ) → History (fun t => Option (E t)) n → E n → ℝ)
    (hk : ∀ n h, ∑ x, k n h x = 1)
    (hf : ∀ n h, live go n h = true → ∑ x, k n h x * f n h x = 0) :
    ∀ N, (∑ h, law (kernel go k) N h * total (score f) N h) = 0 := by
  intro N
  induction N with
  | zero => simp [History, law, total]
  | succ N ih =>
    rw [expected_step _ _ (kernel_normalized go k hk), ih, zero_add]
    apply Finset.sum_eq_zero
    intro h _
    rw [local_moment]
    cases hl : live go N h with
    | false => simp [hl]
    | true => simp [hl, hf N h hl]

/-- Local quadratic costs are charged only while the event program is live.
The right side is its actual expected activity capacity, not N times a
worst-case bound. This identity also applies to nonnegative variance costs. -/
theorem stopped_capacity
    (go : (n : ℕ) → History (fun t => Option (E t)) n → Bool)
    (k f : (n : ℕ) → History (fun t => Option (E t)) n → E n → ℝ)
    (hk : ∀ n h, ∑ x, k n h x = 1) :
    ∀ N, (∑ h, law (kernel go k) N h * total (score f) N h) =
      ∑ n ∈ Finset.range N, ∑ h, law (kernel go k) n h *
        (if live go n h then ∑ x, k n h x * f n h x else 0) := by
  intro N
  induction N with
  | zero => simp [History, law, total]
  | succ N ih =>
    rw [expected_step _ _ (kernel_normalized go k hk), ih, Finset.sum_range_succ]
    congr 1
    apply Finset.sum_congr rfl
    intro h _
    rw [local_moment]

end DRGPR.StoppedEventProgram
#print axioms DRGPR.StoppedEventProgram.terminal_absorbs
#print axioms DRGPR.StoppedEventProgram.dead_stays_dead
#print axioms DRGPR.StoppedEventProgram.kernel_normalized
#print axioms DRGPR.StoppedEventProgram.kernel_nonneg
#print axioms DRGPR.StoppedEventProgram.local_moment
#print axioms DRGPR.StoppedEventProgram.stopped_zero_moment
#print axioms DRGPR.StoppedEventProgram.stopped_capacity
