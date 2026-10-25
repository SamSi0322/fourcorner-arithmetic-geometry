import CommonFieldTensorDomain
import CommonConstantTensorInjection
import CommonTensorFlat

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace FourCorner.CommonGeometricField
open scoped TensorProduct
variable (K L : Type*) [Field K] [Field L] [CharZero K] [Algebra K L]

local instance constantAlgebra (t : K) : Algebra K (CommonLiteralField.field K t) :=
  (CommonLiteralField.field K t).algebra'
local instance constantModule (t : K) : Module K (CommonLiteralField.field K t) :=
  Algebra.toModule

/-- The ACTUAL common four-root field stays a domain after arbitrary extension
of constants. This tensor-product assertion proves geometric integrality,
rather than merely constructing a second field over the new constants. -/
theorem all_constants_domain {t : K} (ht0 : t ≠ 0) (ht1 : t ≠ 1) (htm : t ≠ -1) :
    IsDomain (L ⊗[K] (CommonLiteralField.field K t)) := by
  have : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  letI := CommonFieldTensorDomain.ratAlgebra K L
  letI : Algebra (RatFunc K) (L ⊗[K] RatFunc K) := Algebra.TensorProduct.rightAlgebra
  let f : L ⊗[K] RatFunc K →ₐ[RatFunc K] RatFunc L :=
    { (CommonConstantTensorInjection.tensorMap K L).toRingHom with
      commutes' := by
        intro r
        change (CommonConstantTensorInjection.tensorMap K L) (1 ⊗ₜ[K] r) =
          CommonConstantMap.ratMap K L r
        simp only [CommonConstantTensorInjection.tensorMap,Algebra.TensorProduct.lift_tmul,
          map_one,one_mul]
        rfl }
  letI : IsDomain ((RatFunc L) ⊗[RatFunc K] (CommonLiteralField.field K t)) :=
    CommonFieldTensorDomain.isDomain_rationalFunction_baseChange K L ht0 ht1 htm
  exact CommonTensorFlat.constant_tensor_isDomain_of_rational_tensor_domain f
    (CommonConstantTensorInjection.tensorMap_injective K L)

#print axioms all_constants_domain
end FourCorner.CommonGeometricField
