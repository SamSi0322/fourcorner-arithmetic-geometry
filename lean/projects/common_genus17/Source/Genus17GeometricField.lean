import Genus17TensorComparison
import CommonConstantTensorInjection
import CommonTensorFlat

noncomputable section
namespace FourCorner.Genus17GeometricField
open scoped TensorProduct
open Genus17Geometry
variable (K L : Type*) [Field K] [Field L] [CharZero K] [Algebra K L]
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

local instance constantAlgebra (t κ : K) : Algebra K (field t κ) := modelFieldAlgebra t κ
local instance constantModule (t κ : K) : Module K (field t κ) := Algebra.toModule

/-- The actual five-root field stays a domain after EVERY field extension of
constants, not just after rebuilding its equations over a new field. -/
theorem all_constants_domain {t κ : K} (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1) (hκ : κ ≠ 0) :
    IsDomain (L ⊗[K] (field t κ)) := by
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  letI := CommonFieldTensorDomain.ratAlgebra K L
  letI : Algebra (RatFunc K) (L ⊗[K] RatFunc K) := Algebra.TensorProduct.rightAlgebra
  let f : L ⊗[K] RatFunc K →ₐ[RatFunc K] RatFunc L :=
    { (CommonConstantTensorInjection.tensorMap K L).toRingHom with
      commutes' := by
        intro r
        change (CommonConstantTensorInjection.tensorMap K L) (1 ⊗ₜ[K] r) = CommonConstantMap.ratMap K L r
        simp only [CommonConstantTensorInjection.tensorMap,Algebra.TensorProduct.lift_tmul,map_one,one_mul]
        rfl }
  letI := Genus17TensorComparison.rational_tensor_domain K L h0 h1 hm hκ
  exact CommonTensorFlat.constant_tensor_isDomain_of_rational_tensor_domain f
    (CommonConstantTensorInjection.tensorMap_injective K L)
end FourCorner.Genus17GeometricField
#print axioms FourCorner.Genus17GeometricField.all_constants_domain
