import DependentTransfer
import FiniteController

/- The conditional main theorem, with the paper's directed certificates.
These are the stated model assumptions, not asserted properties of every
reflective deployment. The selection arrow is a proved algorithmic result. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace DRGPR.ModelMain

structure Budget where
  F : ℝ
  G : ℝ
  D_A : ℝ
  D_C : ℝ
  E_nf : ℝ
  E_cpA : ℝ
  E_cpC : ℝ
  T : ℕ
  b : ℕ
  H : ℕ
  N : ℕ
  S : ℕ
  V : ℝ

def Budget.prefix (B : Budget) : ℝ := (B.H:ℝ)*(Nat.ceil ((B.T:ℝ)/(B.b:ℝ))+B.N+1)
def Budget.delta (B : Budget) : ℝ := B.F+B.G+B.D_A+B.D_C+B.E_nf+B.E_cpA+B.E_cpC
def Budget.bound (B : Budget) (η C : ℝ) : ℝ :=
  B.delta+C/η+η*B.b*B.V/2+B.prefix+(B.b:ℝ)*B.S+(B.H:ℝ)*(B.S+1)

variable {Ω : Type*} {I : Ω → ℕ → Type*} [MeasurableSpace Ω]
  [∀ ω r, Fintype (I ω r)] {μ : Measure Ω} [IsProbabilityMeasure μ]

structure Certificates (E : DependentTransfer.Experiment Ω I μ) (B : Budget) where
  realA : Ω → ℝ
  refA : Ω → ℝ
  aligned : Ω → ℝ
  clean : Ω → ℝ
  refPath : Ω → ℝ
  refM : Ω → ℝ
  realM : Ω → ℝ
  cpA : (∫ ω, realA ω ∂μ)-(∫ ω, refA ω ∂μ) ≤ B.E_cpA
  acquisition : (∫ ω, refA ω ∂μ)-E.selectedTotal ≤ B.F+B.prefix+B.D_A
  generation : E.availableTotal-(∫ ω, aligned ω ∂μ) ≤ B.G
  alignment : (∫ ω, aligned ω ∂μ)-(∫ ω, clean ω ∂μ) ≤ (B.b:ℝ)*B.S
  response : (∫ ω, clean ω ∂μ)-(∫ ω, refPath ω ∂μ) ≤ (B.H:ℝ)*(B.S+1)+B.D_C
  representation : (∫ ω, refPath ω ∂μ)-(∫ ω, refM ω ∂μ) ≤ B.E_nf
  cpC : (∫ ω, refM ω ∂μ)-(∫ ω, realM ω ∂μ) ≤ B.E_cpC
  capacity : E.V ≤ (B.b:ℝ)*B.V

theorem main_fixed (E : DependentTransfer.Experiment Ω I μ) (B : Budget)
    (K : Certificates E B) :
    (∫ ω, K.realA ω ∂μ)-(∫ ω, K.realM ω ∂μ) ≤ B.bound E.η E.C := by
  have hs := E.transfer K.realA K.refA K.aligned K.clean K.refPath K.refM K.realM
    B.E_cpA (B.F+B.prefix+B.D_A) B.G ((B.b:ℝ)*B.S)
    ((B.H:ℝ)*(B.S+1)+B.D_C) B.E_nf B.E_cpC
    K.cpA K.acquisition K.generation K.alignment K.response K.representation K.cpC
  have hv := mul_le_mul_of_nonneg_left K.capacity (div_nonneg E.rate_pos.le (by norm_num : (0:ℝ) ≤ 2))
  dsimp [Budget.bound, Budget.delta, DependentTransfer.Experiment.selectionBudget] at *
  nlinarith

theorem main_counterfactual {M : Type*} [Nonempty M]
    (B : Budget) (η C learner : ℝ)
    (E : M → DependentTransfer.Experiment Ω I μ)
    (K : ∀ m, Certificates (E m) B)
    (hrate : ∀ m, (E m).η=η) (hcode : ∀ m, (E m).C=C)
    (hmarginal : ∀ m, (∫ ω, (K m).realA ω ∂μ)=learner) :
    learner-sInf (Set.range (fun m => ∫ ω, (K m).realM ω ∂μ)) ≤ B.bound η C := by
  apply DRGPR.infimum_transfer learner (B.bound η C) _
  · exact Set.range_nonempty _
  · intro x hx
    obtain ⟨m,rfl⟩ := hx
    have h := main_fixed (E m) B (K m)
    simpa [hrate m,hcode m,hmarginal m] using h

/-- A fully recursive finite controller can be connected without assuming an
algorithm_law or a global probability factorization. All comparison endpoints
here are expected losses under the specified respective model laws. -/
theorem finite_controller_transfer {J O : Type} [Fintype J] [Fintype O] [DecidableEq J]
    (A : FiniteController.Program J O)
    (v : (n : ℕ) → SupportedInformation.Hist (J × O) n → J)
    (n : ℕ) (C : ℝ) (B : Budget)
    (hinit : 0 < A.initial.val (v 0 ()))
    (htrans : ∀ r (h : SupportedInformation.Hist (J × O) (r+1)),
      0 < (A.transition r h (v r h.1)).val (v (r+1) h))
    (hcode : ∀ h, -Real.log (A.initial.val (v 0 ()))+
      SupportedInformation.cumulative (A.codeIncrement v) n h ≤ C)
    (hcapacity : A.capacity n ≤ (B.b:ℝ)*B.V)
    (realA refA selected available aligned clean refPath refM realM : ℝ)
    (hgap : selected-available = ∑ h, SupportedInformation.pathLaw A.kernel n h*
      SupportedInformation.cumulative (A.actualGap v) n h)
    (h₁ : realA-refA ≤ B.E_cpA)
    (h₂ : refA-selected ≤ B.F+B.prefix+B.D_A)
    (h₄ : available-aligned ≤ B.G)
    (h₅ : aligned-clean ≤ (B.b:ℝ)*B.S)
    (h₆ : clean-refPath ≤ (B.H:ℝ)*(B.S+1)+B.D_C)
    (h₇ : refPath-refM ≤ B.E_nf)
    (h₈ : refM-realM ≤ B.E_cpC) :
    realA-realM ≤ B.bound A.η C := by
  have hs := A.regret v n C hinit htrans hcode
  rw [← hgap] at hs
  have hv := mul_le_mul_of_nonneg_left hcapacity
    (div_nonneg A.rate_pos.le (by norm_num : (0:ℝ) ≤ 2))
  dsimp [Budget.bound, Budget.delta]
  nlinarith

end DRGPR.ModelMain
#print axioms DRGPR.ModelMain.main_fixed
#print axioms DRGPR.ModelMain.main_counterfactual
#print axioms DRGPR.ModelMain.finite_controller_transfer
