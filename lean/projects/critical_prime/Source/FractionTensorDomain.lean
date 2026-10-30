import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open scoped TensorProduct
namespace FourCorner.FractionTensorDomain
variable (k L A F : Type*) [Field k] [Field L] [CommRing A] [IsDomain A] [Field F]
  [Algebra k L] [Algebra k A] [Algebra k F] [Algebra A F] [IsScalarTower k A F]
  [IsFractionRing A F] [IsDomain (L ⊗[k] A)]

include A

/-- A genuine scalar-extended affine domain remains a domain after passing to
its actual fraction field. The multiplicative set has no zero divisors. -/
theorem tensor_isDomain : IsDomain (L ⊗[k] F) := by
  let T := L ⊗[k] A
  let B := L ⊗[k] F
  let M : Submonoid T := (nonZeroDivisors A).map
    (Algebra.TensorProduct.includeRight (R:=k) (A:=L))
  letI : Algebra T B :=
    (Algebra.TensorProduct.map (AlgHom.id k L) (IsScalarTower.toAlgHom k A F)).toAlgebra
  haveI : IsScalarTower L T B :=
    .of_algebraMap_eq (by
      intro a
      change a ⊗ₜ[k] (1:F) =
        (Algebra.TensorProduct.map (AlgHom.id k L) (IsScalarTower.toAlgHom k A F)) (a ⊗ₜ[k] (1:A))
      simp)
  haveI : IsLocalization M B :=
    IsLocalization.tensorProduct_tensorProduct_right k L (nonZeroDivisors A) F
      (by ext a; simp [RingHom.algebraMap_toAlgebra])
  have hinj : Function.Injective (Algebra.TensorProduct.includeRight : A →ₐ[k] T) :=
    Algebra.TensorProduct.includeRight_injective (algebraMap k L).injective
  apply IsLocalization.isDomain_of_le_nonZeroDivisors (M:=M) B
  exact map_le_nonZeroDivisors_of_injective _ hinj (le_refl _)

end FourCorner.FractionTensorDomain
#print axioms FourCorner.FractionTensorDomain.tensor_isDomain
