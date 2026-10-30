import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.FieldTheory.Minpoly.Field

noncomputable section
open scoped TensorProduct
namespace FourCorner.TensorAlgebraicConstants
variable {K F : Type*} [Field K] [Field F] [Algebra K F]
  [IsDomain (AlgebraicClosure K ⊗[K] F)]
set_option maxHeartbeats 1000000

/-- Geometric tensor integrality forces every element algebraic over the
constant field to be an actual base constant; no rational place is assumed. -/
theorem integral_is_base {x : F} (hx : IsIntegral K x) :
    ∃ c : K, algebraMap K F c = x := by
  let L := AlgebraicClosure K
  let T := L ⊗[K] F
  let iL : L →ₐ[K] T := Algebra.TensorProduct.includeLeft
  let iF : F →ₐ[K] T := Algebra.TensorProduct.includeRight
  let p := (minpoly K x).map (algebraMap K L)
  have hp : p.Monic := (minpoly.monic hx).map _
  have hcomp : iL.toRingHom.comp (algebraMap K L) = algebraMap K T := iL.comp_algebraMap
  have hroot0 : Polynomial.aeval (iF x) (minpoly K x) = 0 := by
    rw [Polynomial.aeval_algHom_apply,minpoly.aeval,map_zero]
  have hroot : (p.map iL.toRingHom).IsRoot (iF x) := by
    change (((minpoly K x).map (algebraMap K L)).map iL.toRingHom).eval (iF x) = 0
    rw [Polynomial.map_map,hcomp]
    simpa only [Polynomial.eval_map,← Polynomial.aeval_def] using hroot0
  obtain ⟨y,hy⟩ := (IsAlgClosed.splits p).mem_range_of_isRoot hp.ne_zero hroot
  change y ⊗ₜ[K] (1 : F) = (1 : L) ⊗ₜ[K] x at hy
  obtain ⟨f,hf⟩ := Module.Projective.exists_dual_eq_one K (one_ne_zero : (1 : F) ≠ 0)
  let projection : T →ₗ[K] L := (TensorProduct.rid K L).toLinearMap.comp
    (TensorProduct.map (LinearMap.id : L →ₗ[K] L) f)
  have hvalue : y = algebraMap K L (f x) := by
    have h := congrArg projection hy
    change f (1 : F) • y = f x • (1 : L) at h
    simpa only [hf,one_smul,Algebra.smul_def,map_one,one_mul,mul_one] using h
  refine ⟨f x,?_⟩
  apply iF.injective
  calc
    iF (algebraMap K F (f x)) = algebraMap K T (f x) := iF.commutes _
    _ = iL (algebraMap K L (f x)) := (iL.commutes _).symm
    _ = iL y := congrArg iL hvalue.symm
    _ = iF x := hy

end FourCorner.TensorAlgebraicConstants
#print axioms FourCorner.TensorAlgebraicConstants.integral_is_base
