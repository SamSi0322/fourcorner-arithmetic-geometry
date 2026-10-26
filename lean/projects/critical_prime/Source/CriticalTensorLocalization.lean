import CriticalFieldConstants
import Slot03HighTensorFraction

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 400000
open scoped TensorProduct
namespace FourCorner.CriticalTensorLocalization
open CriticalRadicalField
variable (k L : Type*) [Field k] [Field L] [Algebra k L]
local instance constantAlgebra (i : k) : Algebra k (field k i) := CriticalFieldConstants.constantAlgebra k i
local instance constantModule (i : k) : Module k (field k i) := CriticalFieldConstants.constantModule k i
local instance towerFieldAlgebra (i : k) : Algebra (tower k i) (field k i) := CriticalFieldConstants.towerFieldAlgebra k i
local instance constantTowerField (i : k) : IsScalarTower k (tower k i) (field k i) := CriticalFieldConstants.constants_tower_field k i

abbrev affineTensor (i : k) := L ⊗[k] tower k i
abbrev fieldTensor (i : k) := L ⊗[k] field k i

def tensorMap (i : k) : affineTensor k L i →ₐ[k] fieldTensor k L i :=
  Algebra.TensorProduct.map (AlgHom.id k L) (IsScalarTower.toAlgHom k (tower k i) (field k i))
abbrev tensorAlgebra (i : k) : Algebra (affineTensor k L i) (fieldTensor k L i) :=
  (tensorMap k L i).toRingHom.toAlgebra

def denominator (i : k) : Submonoid (affineTensor k L i) :=
  (nonZeroDivisors (tower k i)).map (Algebra.TensorProduct.includeRight (R:=k) (A:=L))

theorem tensor_scalar_tower (i : k) :
    letI := tensorAlgebra k L i
    IsScalarTower L (affineTensor k L i) (fieldTensor k L i) := by
  letI := tensorAlgebra k L i
  apply IsScalarTower.of_algebraMap_eq
  intro l
  change l ⊗ₜ[k] (1:field k i)=tensorMap k L i (l ⊗ₜ[k] (1:tower k i))
  simp only [tensorMap,Algebra.TensorProduct.map_tmul,AlgHom.id_apply,map_one]

theorem localization (i : k) (hi : i^2 = -1) (h2 : (2:k) ≠ 0) :
    letI := tensorAlgebra k L i
    IsLocalization (denominator k L i) (fieldTensor k L i) := by
  letI := CriticalFieldConstants.tower_domain k i hi h2
  letI := CriticalFieldConstants.tower_fraction k i hi h2
  letI := tensorAlgebra k L i
  letI := tensor_scalar_tower k L i
  exact IsLocalization.tensorProduct_tensorProduct_right k L (nonZeroDivisors (tower k i)) (field k i)
    (by
      apply RingHom.ext
      intro a
      change tensorMap k L i (1 ⊗ₜ[k] a)=1 ⊗ₜ[k] algebraMap (tower k i) (field k i) a
      simp only [tensorMap,Algebra.TensorProduct.map_tmul,AlgHom.id_apply,
        IsScalarTower.toAlgHom_apply,map_one])

theorem denominator_regular (i : k) (hi : i^2 = -1) (h2 : (2:k) ≠ 0) :
    letI := CriticalFieldConstants.tower_domain k i hi h2
    letI := CriticalFieldConstants.tower_tensor_domain k i hi h2 L
    denominator k L i ≤ nonZeroDivisors (affineTensor k L i) := by
  letI := CriticalFieldConstants.tower_domain k i hi h2
  letI := CriticalFieldConstants.tower_tensor_domain k i hi h2 L
  have hinj : Function.Injective (Algebra.TensorProduct.includeRight : tower k i →ₐ[k] affineTensor k L i) :=
    Algebra.TensorProduct.includeRight_injective (algebraMap k L).injective
  exact map_le_nonZeroDivisors_of_injective _ hinj (le_refl _)

/-- True fraction-field comparison for the actual tensor localization,
with the same left L-constant map and literal right coordinate-field map. -/
def fractionEquiv (i : k) (hi : i^2 = -1) (h2 : (2:k) ≠ 0) :
    letI := CriticalFieldConstants.tower_tensor_domain k i hi h2 L
    letI := CriticalFieldConstants.field_tensor_domain k i hi h2 L
    FractionRing (affineTensor k L i) ≃ₐ[L] FractionRing (fieldTensor k L i) := by
  letI := CriticalFieldConstants.tower_domain k i hi h2
  letI := CriticalFieldConstants.tower_tensor_domain k i hi h2 L
  letI := CriticalFieldConstants.field_tensor_domain k i hi h2 L
  letI := tensorAlgebra k L i
  letI := tensor_scalar_tower k L i
  letI := localization k L i hi h2
  exact Slot03High.fractionLocalizationEquiv L (affineTensor k L i) (fieldTensor k L i)
    (denominator k L i) (denominator_regular k L i hi h2)

end FourCorner.CriticalTensorLocalization
#print axioms FourCorner.CriticalTensorLocalization.localization
#print axioms FourCorner.CriticalTensorLocalization.denominator_regular
#print axioms FourCorner.CriticalTensorLocalization.fractionEquiv
