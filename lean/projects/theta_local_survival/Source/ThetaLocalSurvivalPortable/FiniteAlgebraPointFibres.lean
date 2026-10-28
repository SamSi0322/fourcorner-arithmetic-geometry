import ThetaLocalSurvivalPortable.FiniteAlgebraPointBounds
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped TensorProduct
namespace FourCorner.ThetaLocalSurvival.StrongTopology

variable (A S K : Type) [CommRing A] [CommRing S] [Algebra ℚ A]
  [Algebra A S] [Algebra ℚ S] [IsScalarTower ℚ A S]
  [Field K] [Algebra ℚ K] [Module.Finite A S]

/-- The fibre of the actual affine finite-algebra point map over every actual base
point is finite, by the genuine finite-dimensional scalar-extended algebra. -/
theorem finite_algebra_point_fibres (φ : A →ₐ[ℚ] K) :
    {f : S →ₐ[ℚ] K | f.comp (Algebra.algHom ℚ A S)=φ}.Finite := by
  letI : Algebra A K := φ.toRingHom.toAlgebra
  letI : IsScalarTower ℚ A K := IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  letI : Finite (S →ₐ[A] K) := Finite.of_injective
    (AlgHom.liftEquiv A K S K) (AlgHom.liftEquiv A K S K).injective
  let encode : {f : S →ₐ[ℚ] K // f.comp (Algebra.algHom ℚ A S)=φ} → (S →ₐ[A] K) :=
    fun f => { f.1.toRingHom with
      commutes' := by
        intro a
        exact congrArg (fun g : A →ₐ[ℚ] K => g a) f.2 }
  have hinj : Function.Injective encode := by
    intro f g h
    apply Subtype.ext
    apply AlgHom.ext
    intro s
    exact congrArg (fun f : S →ₐ[A] K => f s) h
  exact Set.finite_coe_iff.mp (Finite.of_injective encode hinj)

end FourCorner.ThetaLocalSurvival.StrongTopology
