import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Analysis.Calculus.ImplicitFunction.ProdDomain

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped Topology BigOperators
open MvPolynomial
namespace FourCorner.ThetaLocalSurvival.StrongTopology

variable {K : Type*} [NontriviallyNormedField K]
  {ι : Type*} [Fintype ι]

/-- The actual derivative of multivariable polynomial evaluation over any normed field. -/
def polynomialGradient (p : MvPolynomial ι K) (x : ι → K) : (ι → K) →L[K] K :=
  ∑ i, (eval x (pderiv i p)) • ContinuousLinearMap.proj i

theorem polynomialGradient_apply (p : MvPolynomial ι K) (x v : ι → K) :
    polynomialGradient p x v = ∑ i, eval x (pderiv i p) * v i := by
  simp [polynomialGradient,ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply]

/-- Strict differentiability and the formal partial derivative formula hold also over Q_p. -/
theorem hasStrictFDerivAt_polynomialEval (p : MvPolynomial ι K) (x : ι → K) :
    HasStrictFDerivAt (fun y => eval y p) (polynomialGradient p x) x := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a =>
      have h := hasStrictFDerivAt_const (𝕜:=K) a x
      simpa [polynomialGradient] using h
  | add p q hp hq =>
      have h := hp.add hq
      have he : polynomialGradient p x + polynomialGradient q x = polynomialGradient (p+q) x := by
        ext v
        simp [polynomialGradient_apply,Finset.sum_add_distrib,add_mul]
      rw [he] at h
      convert h using 1 <;> first | rfl | (funext y; exact eval_add)
  | mul_X p i hp =>
      have h := hp.mul (ContinuousLinearMap.hasStrictFDerivAt (ContinuousLinearMap.proj i) (x:=x))
      have he : eval x p • ContinuousLinearMap.proj i + x i • polynomialGradient p x =
          polynomialGradient (p * X i) x := by
        ext v
        simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
          ContinuousLinearMap.proj_apply,smul_eq_mul,polynomialGradient_apply]
        have hxj (j : ι) : eval x (pderiv j (X i : MvPolynomial ι K)) =
            if j=i then 1 else 0 := by
          simp [pderiv_X,Pi.single_apply,eq_comm]
        simp_rw [pderiv_mul,map_add,eval_mul,eval_X,hxj]
        simp only [add_mul,mul_ite,ite_mul,mul_one,mul_zero,zero_mul,
          Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,if_true]
        rw [Finset.mul_sum,add_comm]
        congr 1
        apply Finset.sum_congr rfl
        intro j _
        ring
      change HasStrictFDerivAt (fun y => eval y p * y i)
        (eval x p • ContinuousLinearMap.proj i + x i • polynomialGradient p x) x at h
      rw [he] at h
      simpa only [eval_mul,eval_X] using h

end FourCorner.ThetaLocalSurvival.StrongTopology
