import ErasedBandit

noncomputable section
open scoped BigOperators
namespace DRGPR.TableDistribution
open ErasedBandit
variable {I : Type} [Fintype I] [DecidableEq I]

def row (p : I → ℝ) (x : I → Bool) : ℝ := ∏ i, bernoulli (p i) (x i)

theorem row_normalized (p : I → ℝ) : (∑ x, row p x)=1 := by
  unfold row
  rw [← Fintype.prod_sum]
  simp [bernoulli,Fintype.sum_bool]

theorem row_nonneg (p : I → ℝ) (hp : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) (x : I → Bool) :
    0 ≤ row p x := by
  apply Finset.prod_nonneg
  intro i _
  cases x i <;> simp only [bernoulli] <;> linarith [hp i,hp1 i]

theorem coordinate_expectation (p : I → ℝ) (i : I) (g : Bool → ℝ) :
    (∑ x, row p x*g (x i))=∑ b, bernoulli (p i) b*g b := by
  let aug := fun k b => bernoulli (p k) b*(if k=i then g b else 1)
  have hprod (x : I → Bool) : row p x*g (x i)=∏ k, aug k (x k) := by
    dsimp [row,aug]
    rw [Finset.prod_mul_distrib]
    simp
  simp_rw [hprod]
  rw [← Fintype.prod_sum]
  have hsum (k : I) : (∑ b, aug k b)=
      if k=i then (∑ b, bernoulli (p i) b*g b) else 1 := by
    by_cases hk : k=i
    · subst k; simp [aug]
    · simp [aug,hk,bernoulli,Fintype.sum_bool]
  simp_rw [hsum]
  simp

theorem coordinate_marginal (p : I → ℝ) (i : I) (b : Bool) :
    (∑ x, if x i=b then row p x else 0)=bernoulli (p i) b := by
  have h := coordinate_expectation p i (fun a => if a=b then 1 else 0)
  simpa [mul_ite,Fintype.sum_bool] using h

theorem coordinate_loss (p : I → ℝ) (i : I) :
    (∑ x, row p x*(if x i then (0:ℝ) else 1))=p i := by
  have h := coordinate_expectation p i (fun b => if b then 0 else 1)
  simpa [bernoulli,Fintype.sum_bool] using h

end DRGPR.TableDistribution
#print axioms DRGPR.TableDistribution.row_normalized
#print axioms DRGPR.TableDistribution.row_nonneg
#print axioms DRGPR.TableDistribution.coordinate_expectation
#print axioms DRGPR.TableDistribution.coordinate_marginal
#print axioms DRGPR.TableDistribution.coordinate_loss
