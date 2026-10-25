import ResidueTensorComparison
import CommonConstantTensorInjection
import CommonTensorFlat

noncomputable section
namespace FourCorner.ResidueGeometricField
open scoped TensorProduct
open Genus17Geometry
variable (K L : Type*) [Field K] [Field L] [NeZero (2 : K)] [Algebra K L]
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

local instance constantAlgebra (t κ : K) : Algebra K (field t κ) := modelFieldAlgebra t κ
local instance constantModule (t κ : K) : Module K (field t κ) := Algebra.toModule

/-- The actual five-root field stays a domain after EVERY field extension of
constants, not just after rebuilding its equations over a new field. -/
theorem all_constants_domain {t κ : K} (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1) (hκ : κ ≠ 0) :
    IsDomain (L ⊗[K] (field t κ)) := by
  haveI : NeZero (2 : L) := ⟨by
    intro h
    exact NeZero.ne (2 : K) ((algebraMap K L).injective
      (by simpa only [map_ofNat,map_zero] using h))⟩
  letI := CommonFieldTensorDomain.ratAlgebra K L
  letI : Algebra (RatFunc K) (L ⊗[K] RatFunc K) := Algebra.TensorProduct.rightAlgebra
  let f : L ⊗[K] RatFunc K →ₐ[RatFunc K] RatFunc L :=
    { (CommonConstantTensorInjection.tensorMap K L).toRingHom with
      commutes' := by
        intro r
        change (CommonConstantTensorInjection.tensorMap K L) (1 ⊗ₜ[K] r) = CommonConstantMap.ratMap K L r
        simp only [CommonConstantTensorInjection.tensorMap,Algebra.TensorProduct.lift_tmul,map_one,one_mul]
        rfl }
  letI := ResidueTensorComparison.rational_tensor_domain K L h0 h1 hm hκ
  exact CommonTensorFlat.constant_tensor_isDomain_of_rational_tensor_domain f
    (CommonConstantTensorInjection.tensorMap_injective K L)
end FourCorner.ResidueGeometricField
#print axioms FourCorner.ResidueGeometricField.all_constants_domain
