import GrowingPotential
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! Expected growing selection on an arbitrary probability space. Conditional
moment and integrability contracts are explicit. No finite sample-space or
finite observation-space restriction is used. Identity types remain finite. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace DRGPR.GeneralSelection

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

theorem equal_integrals_of_condExp {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    (f g : Ω → ℝ) (h : μ[f|m] =ᵐ[μ] μ[g|m]) :
    (∫ ω, f ω ∂μ) = ∫ ω, g ω ∂μ := by
  calc
    _ = ∫ ω, μ[f|m] ω ∂μ := (integral_condExp hm).symm
    _ = ∫ ω, μ[g|m] ω ∂μ := integral_congr_ae h
    _ = _ := integral_condExp hm

theorem integrate_potential (f s Q : Ω → ℝ) (c a V : ℝ)
    (hf : Integrable f μ) (hs : Integrable s μ) (hQ : Integrable Q μ)
    (ha : 0 ≤ a) (hlinear : (∫ ω, f ω ∂μ) = ∫ ω, s ω ∂μ)
    (hpoint : ∀ᵐ ω ∂μ, f ω ≤ c+a*Q ω)
    (hvar : (∫ ω, Q ω ∂μ) ≤ V) :
    (∫ ω, s ω ∂μ) ≤ c+a*V := by
  have hi := integral_mono_ae hf ((integrable_const c).add (hQ.const_mul a)) hpoint
  change (∫ ω, f ω ∂μ) ≤ ∫ ω, c+a*Q ω ∂μ at hi
  rw [integral_add (integrable_const c) (hQ.const_mul a), integral_const_mul,
    integral_const] at hi
  simp only [Measure.real, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul] at hi
  rw [hlinear] at hi
  exact le_trans hi (add_le_add_left (mul_le_mul_of_nonneg_left hvar ha) c)

variable {ι : ℕ → Type*} [∀ r, Fintype (ι r)]

def linear (ν : Ω → ι 0 → ℝ) (P : ∀ (ω : Ω) r, ι r → ι (r+1) → ℝ)
    (z : ∀ (ω : Ω) r, ι r → ℝ) (η : ℝ) (v : ∀ (ω : Ω) r, ι r) (r : ℕ) (ω : Ω) : ℝ :=
  mean (Growing.prob (ν ω) (P ω) (z ω) η r) (z ω r)-z ω r (v ω r)

def square (ν : Ω → ι 0 → ℝ) (P : ∀ (ω : Ω) r, ι r → ι (r+1) → ℝ)
    (z : ∀ (ω : Ω) r, ι r → ℝ) (η : ℝ) (r : ℕ) (ω : Ω) : ℝ :=
  mean (Growing.prob (ν ω) (P ω) (z ω) η r) (fun i => (z ω r i)^2)

theorem expected_growing_selection
    (ν : Ω → ι 0 → ℝ) (P : ∀ ω r, ι r → ι (r+1) → ℝ)
    (z : ∀ ω r, ι r → ℝ) (η C V : ℝ) (R : ℕ)
    (v : ∀ ω r, ι r) (s : ℕ → Ω → ℝ)
    (hη : 0 < η)
    (hν : ∀ ω i, 0 ≤ ν ω i) (hν1 : ∀ ω, ∑ i, ν ω i=1)
    (hP : ∀ ω r i j, 0 ≤ P ω r i j)
    (hP1 : ∀ ω r i, ∑ j, P ω r i j=1)
    (hz : ∀ ω r i, 0 ≤ z ω r i)
    (hv0 : ∀ ω, 0 < ν ω (v ω 0))
    (hvP : ∀ ω r, 0 < P ω r (v ω r) (v ω (r+1)))
    (hcode : ∀ ω, -(Real.log (ν ω (v ω 0))+
      ∑ r ∈ Finset.range R, Real.log (P ω r (v ω r) (v ω (r+1)))) ≤ C)
    (hi : ∀ r, Integrable (linear ν P z η v r) μ)
    (hs : ∀ r, Integrable (s r) μ)
    (hq : ∀ r, Integrable (square ν P z η r) μ)
    (hmoment : ∀ r, (∫ ω, linear ν P z η v r ω ∂μ) = ∫ ω, s r ω ∂μ)
    (hvariance : (∑ r ∈ Finset.range (R+1), ∫ ω, square ν P z η r ω ∂μ) ≤ V) :
    (∑ r ∈ Finset.range (R+1), ∫ ω, s r ω ∂μ) ≤ C/η+η*V/2 := by
  classical
  have hpoint (ω : Ω) :
      (∑ r ∈ Finset.range (R+1), linear ν P z η v r ω) ≤
        C/η+(η/2)*(∑ r ∈ Finset.range (R+1), square ν P z η r ω) := by
    have hp := Growing.growing_path_regret (ν ω) (P ω) (z ω) η
      (hν ω) (hν1 ω) (hP ω) (hP1 ω) hη (hz ω) (v ω) (hv0 ω) (hvP ω) R
    simp only [linear, square, Finset.sum_sub_distrib]
    exact le_trans hp (add_le_add_right
      (div_le_div_of_nonneg_right (hcode ω) hη.le) _)
  have hlin : (∫ ω, ∑ r ∈ Finset.range (R+1), linear ν P z η v r ω ∂μ) =
      ∫ ω, ∑ r ∈ Finset.range (R+1), s r ω ∂μ := by
    rw [integral_finset_sum _ (fun r _ => hi r), integral_finset_sum _ (fun r _ => hs r)]
    exact Finset.sum_congr rfl (fun r _ => hmoment r)
  have hvar : (∫ ω, ∑ r ∈ Finset.range (R+1), square ν P z η r ω ∂μ) ≤ V := by
    rw [integral_finset_sum _ (fun r _ => hq r)]
    exact hvariance
  have ht := integrate_potential μ _ _ _ (C/η) (η/2) V
    (integrable_finset_sum _ (fun r _ => hi r))
    (integrable_finset_sum _ (fun r _ => hs r))
    (integrable_finset_sum _ (fun r _ => hq r))
    (by positivity) hlin (Filter.Eventually.of_forall hpoint) hvar
  rw [integral_finset_sum _ (fun r _ => hs r)] at ht
  convert ht using 1 <;> ring

end DRGPR.GeneralSelection
#print axioms DRGPR.GeneralSelection.equal_integrals_of_condExp
#print axioms DRGPR.GeneralSelection.integrate_potential
#print axioms DRGPR.GeneralSelection.expected_growing_selection
