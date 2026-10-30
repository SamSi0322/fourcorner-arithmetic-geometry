import ThetaCoverClassPortable.PolynomialStrictDerivative
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped Topology BigOperators
open MvPolynomial Filter
namespace FourCorner.ThetaLocalSurvival.StrongTopology

variable {K : Type*} [NontriviallyNormedField K]
  {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

def matrixCLM (M : Matrix β α K) : (α → K) →L[K] (β → K) :=
  ContinuousLinearMap.pi (fun i => ∑ j, M i j • ContinuousLinearMap.proj j)

theorem matrixCLM_apply (M : Matrix β α K) (v : α → K) :
    matrixCLM M v=M.mulVec v := by
  ext i
  simp [matrixCLM,Matrix.mulVec,dotProduct,ContinuousLinearMap.sum_apply]

theorem matrixCLM_comp (M : Matrix γ β K) (N : Matrix β α K) :
    matrixCLM M ∘L matrixCLM N=matrixCLM (M*N) := by
  ext v i
  simp only [ContinuousLinearMap.comp_apply,matrixCLM_apply,Matrix.mulVec_mulVec]

theorem matrixCLM_one [DecidableEq β] : matrixCLM (1 : Matrix β β K)=.id K (β→K) := by
  ext v i
  simp [matrixCLM_apply]

theorem matrixCLM_isInvertible [DecidableEq β] (M : Matrix β β K) (h : M.det≠0) :
    (matrixCLM M).IsInvertible := by
  have hu : IsUnit M.det := isUnit_iff_ne_zero.mpr h
  apply ContinuousLinearMap.IsInvertible.of_inverse (g:=matrixCLM M⁻¹)
  · rw [matrixCLM_comp,M.mul_nonsing_inv hu,matrixCLM_one]
  · rw [matrixCLM_comp,M.nonsing_inv_mul hu,matrixCLM_one]

/-- The ordinary continuous linear concatenation of parameter and unknown coordinates. -/
def concatCLM : ((α→K)×(β→K)) →L[K] (α⊕β→K) :=
  ContinuousLinearMap.pi (Sum.elim
    (fun i => (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.fst K _ _))
    (fun i => (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd K _ _)))

theorem concatCLM_apply (u : (α→K)×(β→K)) : concatCLM u=Sum.elim u.1 u.2 := by
  funext i
  cases i <;> simp [concatCLM]

def polynomialSystem (Q : β → MvPolynomial (α⊕β) K) (u : (α→K)×(β→K)) : β→K :=
  fun i => eval (Sum.elim u.1 u.2) (Q i)

def polynomialSystemDerivative (Q : β → MvPolynomial (α⊕β) K) (u : (α→K)×(β→K)) :
    ((α→K)×(β→K)) →L[K] (β→K) :=
  ContinuousLinearMap.pi (fun i => (polynomialGradient (Q i) (Sum.elim u.1 u.2)).comp concatCLM)

theorem hasStrictFDerivAt_polynomialSystem (Q : β → MvPolynomial (α⊕β) K)
    (u : (α→K)×(β→K)) :
    HasStrictFDerivAt (polynomialSystem Q) (polynomialSystemDerivative Q u) u := by
  apply hasStrictFDerivAt_pi.mpr
  intro i
  have h := (hasStrictFDerivAt_polynomialEval (Q i) (concatCLM u)).comp u
    (concatCLM.hasStrictFDerivAt (x:=u))
  simp only [concatCLM_apply] at h
  exact h

/-- The actual Jacobian in the unknown coordinates, evaluated at the given point. -/
def polynomialUnknownJacobian (Q : β → MvPolynomial (α⊕β) K)
    (u : (α→K)×(β→K)) : Matrix β β K :=
  fun i j => eval (Sum.elim u.1 u.2) (pderiv (.inr j) (Q i))

theorem polynomialSystemDerivative_inr (Q : β → MvPolynomial (α⊕β) K)
    (u : (α→K)×(β→K)) :
    polynomialSystemDerivative Q u ∘L ContinuousLinearMap.inr K (α→K) (β→K) =
      matrixCLM (polynomialUnknownJacobian Q u) := by
  ext v i
  simp [polynomialSystemDerivative,polynomialGradient_apply,concatCLM_apply,
    polynomialUnknownJacobian,matrixCLM_apply,Matrix.mulVec,dotProduct,Fintype.sum_sum_type]

/-- Actual parametric polynomial IFT over every complete nontrivially normed field,
including every Q_p. The equations and their evaluated Jacobian are explicit. -/
theorem polynomial_implicit_neighborhood [CompleteSpace K] [DecidableEq β]
    (Q : β → MvPolynomial (α⊕β) K) (u : (α→K)×(β→K))
    (hzero : polynomialSystem Q u=0) (hdet : (polynomialUnknownJacobian Q u).det≠0) :
    ∃ ψ : (α→K) → (β→K),
      ψ u.1=u.2 ∧ ContinuousAt ψ u.1 ∧
      (∀ᶠ v in 𝓝 u, polynomialSystem Q v=0 ↔ ψ v.1=v.2) ∧
      (∀ᶠ c in 𝓝 u.1, polynomialSystem Q (c,ψ c)=0) := by
  have hd := hasStrictFDerivAt_polynomialSystem Q u
  have hi : (polynomialSystemDerivative Q u ∘L ContinuousLinearMap.inr K (α→K) (β→K)).IsInvertible := by
    rw [polynomialSystemDerivative_inr]
    exact matrixCLM_isInvertible _ hdet
  let ψ := hd.implicitFunctionOfProdDomain hi
  have he := hd.eventually_apply_eq_iff_implicitFunctionOfProdDomain hi
  refine ⟨ψ,?_,?_,?_,?_⟩
  · exact he.self_of_nhds.mp rfl
  · exact (hd.hasStrictFDerivAt_implicitFunctionOfProdDomain hi).continuousAt
  · simpa only [hzero] using he
  · simpa only [hzero] using hd.eventually_apply_implicitFunctionOfProdDomain hi

end FourCorner.ThetaLocalSurvival.StrongTopology
