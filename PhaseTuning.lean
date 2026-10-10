import DRGPR
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.Order.Floor.Semiring

/-! The corrected run-cap calculation, including both clipping cases.
This verifies tuning an already established finite-phase bound. It does
not, by itself, prove the full minimax upper or lower theorem. -/
noncomputable section
namespace DRGPR.PhaseTuning

def cap (n : ℕ) (x : ℝ) : ℕ := min n (max 1 (Nat.ceil x))

theorem cap_eq_ceil (n : ℕ) (x : ℝ) (hx : 0 < x) (hxn : x ≤ n) :
    cap n x = Nat.ceil x := by
  have h1 : 1 ≤ Nat.ceil x := Nat.one_le_ceil_iff.mpr hx
  have hn : Nat.ceil x ≤ n := Nat.ceil_le.mpr hxn
  simp only [cap, max_eq_right h1, min_eq_right hn]

theorem cap_bounds (n : ℕ) (x : ℝ) (hx : 0 < x) (hxn : x ≤ n) :
    x ≤ (cap n x : ℝ) ∧ (cap n x : ℝ) < x+1 := by
  rw [cap_eq_ceil n x hx hxn]
  exact ⟨Nat.le_ceil x, Nat.ceil_lt_add_one hx.le⟩

theorem cap_small (n : ℕ) (x : ℝ) (hn : 1 ≤ n) (hx : 0 < x) (hx1 : x < 1) :
    cap n x = 1 := by
  have hceil : Nat.ceil x = 1 := le_antisymm
    (Nat.ceil_le.mpr (by simpa using hx1.le)) (Nat.one_le_ceil_iff.mpr hx)
  simp only [cap, hceil, max_self, min_eq_right hn]

theorem balance_square (a n x : ℝ) (hx : 0 < x) (hbal : a*x^3=n) :
    a*n*x=(n/x)^2 := by
  rw [div_pow]
  apply (eq_div_iff (pow_ne_zero 2 hx.ne')).2
  calc
    a*n*x*x^2 = n*(a*x^3) := by ring
    _ = n*n := by rw [hbal]
    _ = n^2 := by ring

theorem root_pos_cube (a n : ℝ) (ha : 0 < a) (hn : 0 < n) :
    0 < (n/a)^((1:ℝ)/3) ∧ a*((n/a)^((1:ℝ)/3))^3=n := by
  constructor
  · exact Real.rpow_pos_of_pos (div_pos hn ha) _
  · have hc : ((n/a)^((1:ℝ)/3))^3=n/a := by
      rw [← Real.rpow_mul_natCast (div_nonneg hn.le ha.le)]
      norm_num
    rw [hc]
    field_simp

theorem root_le_n (a n x : ℝ) (ha : 1 ≤ a) (hn : 1 ≤ n)
    (hx : 0 < x) (hbal : a*x^3=n) : x ≤ n := by
  have hc : x^3 ≤ n := by
    have h := mul_nonneg (sub_nonneg.mpr ha) (pow_nonneg hx.le 3)
    nlinarith
  by_contra h
  have hxn : n < x := lt_of_not_ge h
  have hx1 : 1 ≤ x := by linarith
  have hs : 1 ≤ x^2 := by nlinarith [sq_nonneg (x-1)]
  have ht := mul_nonneg hx.le (sub_nonneg.mpr hs)
  nlinarith

theorem root_scale (a n : ℝ) (ha : 0 < a) (hn : 0 < n) :
    n/((n/a)^((1:ℝ)/3)) = a^((1:ℝ)/3)*n^((2:ℝ)/3) := by
  rw [Real.div_rpow hn.le ha.le]
  have hp : n^((1:ℝ)/3)*n^((2:ℝ)/3)=n := by
    rw [← Real.rpow_add hn]
    norm_num
  have hnroot : n^((1:ℝ)/3) ≠ 0 := (Real.rpow_pos_of_pos hn _).ne'
  have haroot : a^((1:ℝ)/3) ≠ 0 := (Real.rpow_pos_of_pos ha _).ne'
  apply (div_eq_iff (div_ne_zero hnroot haroot)).2
  field_simp
  calc
    n * a^((1:ℝ)/3) = a^((1:ℝ)/3) * (n^((1:ℝ)/3)*n^((2:ℝ)/3)) := by rw [hp]; ring
    _ = a^((1:ℝ)/3)*n^((2:ℝ)/3)*n^((1:ℝ)/3) := by ring

theorem sqrt_double_le (u v : ℝ) (hu : 0 ≤ u) (huv : u ≤ v) :
    Real.sqrt (2*u) ≤ (3/2:ℝ)*Real.sqrt v := by
  have hv : 0 ≤ v := le_trans hu huv
  apply (Real.sqrt_le_left (by positivity)).2
  have hs := Real.sq_sqrt hv
  nlinarith

theorem phase_bound_root (a q : ℝ) (n : ℕ) (x : ℝ)
    (ha : 1 ≤ a) (hn : 1 ≤ n) (hq : 0 < q) (hq1 : q ≤ 1)
    (hx : 0 < x) (hbal : a*x^3=(n:ℝ)) :
    Real.sqrt (2*a*n*(cap n x : ℝ)) + Real.sqrt (2*a*n/q) +
      (n:ℝ)/(cap n x : ℝ)+2 ≤
      4*((n:ℝ)/x+Real.sqrt (a*n/q)+1) := by
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) ha
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ) < n := lt_of_lt_of_le (by norm_num) hn1
  have hv : 0 ≤ a*n/q := by positivity
  have hu : 0 ≤ (n:ℝ)/x := by positivity
  have hinfo : Real.sqrt (2*a*n/q) ≤ (3/2:ℝ)*Real.sqrt (a*n/q) := by
    have h := sqrt_double_le (a*n/q) (a*n/q) hv le_rfl
    convert h using 1 <;> congr 1 <;> ring
  have han : a*(n:ℝ) ≤ a*n/q := by
    apply (le_div_iff₀ hq).2
    nlinarith [mul_nonneg (mul_nonneg ha0.le hn0.le) (sub_nonneg.mpr hq1)]
  by_cases hx1 : 1 ≤ x
  · have hxn := root_le_n a n x ha hn1 hx hbal
    obtain ⟨hblo,hbhi⟩ := cap_bounds n x hx hxn
    have hb2 : (cap n x:ℝ) ≤ 2*x := by linarith
    have hb0 : (0:ℝ) < cap n x := lt_of_lt_of_le hx hblo
    have hbalance := balance_square a n x hx hbal
    have hsel : Real.sqrt (2*a*n*(cap n x:ℝ)) ≤ 2*((n:ℝ)/x) := by
      apply (Real.sqrt_le_left (by positivity)).2
      have h := mul_le_mul_of_nonneg_left hb2 (by positivity : 0 ≤ 2*a*(n:ℝ))
      nlinarith [hbalance]
    have hswitch : (n:ℝ)/(cap n x:ℝ) ≤ (n:ℝ)/x :=
      div_le_div_of_nonneg_left hn0.le hx hblo
    have hs0 := Real.sqrt_nonneg (a*n/q)
    nlinarith
  · have hxlt : x < 1 := lt_of_not_ge hx1
    rw [cap_small n x hn hx hxlt]
    norm_num only [Nat.cast_one, mul_one, div_one]
    have hx2 : x^2 < 1 := by nlinarith [mul_pos hx (sub_pos.mpr hxlt)]
    have hx3 : x^3 < 1 := by
      have h := mul_pos (pow_pos hx 2) (sub_pos.mpr hxlt)
      nlinarith
    have hna : (n:ℝ) < a := by
      have h := mul_pos ha0 (sub_pos.mpr hx3)
      nlinarith [hbal]
    have hnSq : (n:ℝ)^2 ≤ a*n/q := by
      have h : (n:ℝ)^2 ≤ a*n := by nlinarith
      exact le_trans h han
    have hnSqrt : (n:ℝ) ≤ Real.sqrt (a*n/q) := by
      have hs := Real.sq_sqrt hv
      have hs0 := Real.sqrt_nonneg (a*n/q)
      nlinarith
    have hsel : Real.sqrt (2*a*n) ≤ (3/2:ℝ)*Real.sqrt (a*n/q) := by
      have h := sqrt_double_le (a*n) (a*n/q) (by positivity) han
      convert h using 1 <;> congr 1 <;> ring
    have hs0 := Real.sqrt_nonneg (a*n/q)
    nlinarith

theorem corrected_phase_bound (a q : ℝ) (n : ℕ)
    (ha : 1 ≤ a) (hn : 1 ≤ n) (hq : 0 < q) (hq1 : q ≤ 1) :
    let x := ((n:ℝ)/a)^((1:ℝ)/3)
    Real.sqrt (2*a*n*(cap n x:ℝ)) + Real.sqrt (2*a*n/q) +
      (n:ℝ)/(cap n x:ℝ)+2 ≤
      4*(a^((1:ℝ)/3)*(n:ℝ)^((2:ℝ)/3)+Real.sqrt (a*n/q)+1) := by
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) ha
  have hn0 : (0:ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 1) hn)
  obtain ⟨hx,hbal⟩ := root_pos_cube a n ha0 hn0
  have h := phase_bound_root a q n _ ha hn hq hq1 hx hbal
  rw [root_scale a n ha0 hn0] at h
  exact h

end DRGPR.PhaseTuning

#print axioms DRGPR.PhaseTuning.cap_eq_ceil
#print axioms DRGPR.PhaseTuning.cap_bounds
#print axioms DRGPR.PhaseTuning.cap_small
#print axioms DRGPR.PhaseTuning.balance_square
#print axioms DRGPR.PhaseTuning.root_pos_cube
#print axioms DRGPR.PhaseTuning.root_le_n
#print axioms DRGPR.PhaseTuning.root_scale
#print axioms DRGPR.PhaseTuning.sqrt_double_le
#print axioms DRGPR.PhaseTuning.phase_bound_root
#print axioms DRGPR.PhaseTuning.corrected_phase_bound
