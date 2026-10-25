import FourCorner.HasseNormWitness
import Mathlib.RingTheory.Norm.Defs
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic
namespace FourCorner.SqrtTwoFieldNorm
open HasseNormWitness

/-- The quadratic polynomial X²−2 has no rational root. -/
instance noRationalRootTwo : Fact (∀ r : ℚ, r^2 ≠ (2 : ℚ)+0*r) := ⟨by
  intro r hr
  have hns : ¬ IsSquare (2 : ℚ) := by norm_num
  apply hns
  refine ⟨r,?_⟩
  simpa only [zero_mul,add_zero,pow_two] using hr.symm⟩

/-- Thus the standard rank-two algebra used for our witnesses is the actual
quadratic number field Q(√2), with its canonical field structure. -/
example : Field (SqrtTwo ℚ) := inferInstance

/-- The standard multiplicative quadratic norm equals the determinant norm
of multiplication. Proof adapted from Mathlib's NormDeterminant theorem. -/
theorem algebra_norm_eq {K : Type*} [Field K] (z : SqrtTwo K) :
    Algebra.norm K z = z.norm := by
  rw [Algebra.norm_apply]
  change (DistribSMul.toLinearMap K (SqrtTwo K) z).det = z.norm
  rw [← LinearMap.det_toMatrix (QuadraticAlgebra.basis 2 0)]
  have hh : (!![z.re, 2*z.im; z.im,z.re] : Matrix (Fin 2) (Fin 2) K).det = z.norm := by
    simp [QuadraticAlgebra.norm]
  convert hh using 1
  apply congrArg Matrix.det
  apply LinearEquiv.eq_symm_apply (LinearMap.toMatrix (QuadraticAlgebra.basis 2 0)
    (QuadraticAlgebra.basis 2 0)) |>.mp
  ext1 w
  apply (QuadraticAlgebra.basis 2 0).repr.injective
  apply DFunLike.coe_injective
  rw [LinearMap.toMatrix_symm,Matrix.repr_toLin]
  ext i
  fin_cases i <;> simp <;> ring

/-- A witness from this development is a genuine field norm witness. -/
theorem exists_field_norm (r : ℚ) (h : ∃ x : SqrtTwo ℚ, x.norm=r) :
    ∃ x : SqrtTwo ℚ, Algebra.norm ℚ x=r := by
  obtain ⟨x,hx⟩ := h
  exact ⟨x,(algebra_norm_eq x).trans hx⟩
#print axioms algebra_norm_eq
#print axioms exists_field_norm
end FourCorner.SqrtTwoFieldNorm
