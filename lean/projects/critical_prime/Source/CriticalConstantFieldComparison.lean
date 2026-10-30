import CriticalTensorLocalization

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 400000
open scoped TensorProduct
namespace FourCorner.CriticalConstantFieldComparison
open CriticalRadicalField
variable (k L : Type*) [Field k] [Field L] [Algebra k L]
local instance sourceConstantAlgebra (i : k) : Algebra k (field k i) := CriticalFieldConstants.constantAlgebra k i
local instance sourceConstantModule (i : k) : Module k (field k i) := CriticalFieldConstants.constantModule k i
local instance targetConstantAlgebra (i : k) : Algebra L (field L (algebraMap k L i)) :=
  CriticalFieldConstants.constantAlgebra L (algebraMap k L i)
local instance targetConstantModule (i : k) : Module L (field L (algebraMap k L i)) :=
  CriticalFieldConstants.constantModule L (algebraMap k L i)
local instance targetTowerAlgebra (i : k) : Algebra (tower L (algebraMap k L i)) (field L (algebraMap k L i)) :=
  CriticalFieldConstants.towerFieldAlgebra L (algebraMap k L i)
local instance targetTowerScalars (i : k) : IsScalarTower L (tower L (algebraMap k L i)) (field L (algebraMap k L i)) :=
  CriticalFieldConstants.constants_tower_field L (algebraMap k L i)

theorem mapped_hypotheses (i : k) (hi : i^2 = -1) (h2 : (2:k) ≠ 0) :
    (algebraMap k L i)^2 = -1 ∧ (2:L) ≠ 0 := by
  constructor
  · simpa only [map_pow,map_neg,map_one] using congrArg (algebraMap k L) hi
  · simpa only [map_ofNat] using (map_ne_zero (algebraMap k L)).mpr h2

/-- The fraction field of the ACTUAL field-constant tensor is the SAME
literal two-root field at the mapped i. The comparison is constructed from
actual tensor localization and the literal ordered coordinate-tower map.
No perfectness, characteristic-zero, comparison or genus premise is used. -/
def fractionFieldEquiv (i : k) (hi : i^2 = -1) (h2 : (2:k) ≠ 0) :
    letI := CriticalFieldConstants.field_tensor_domain k i hi h2 L
    FractionRing (L ⊗[k] field k i) ≃ₐ[L] field L (algebraMap k L i) := by
  letI := CriticalFieldConstants.field_tensor_domain k i hi h2 L
  letI := CriticalFieldConstants.tower_tensor_domain k i hi h2 L
  have hL := mapped_hypotheses k L i hi h2
  letI := CriticalFieldConstants.tower_domain L (algebraMap k L i) hL.1 hL.2
  letI := CriticalFieldConstants.tower_fraction L (algebraMap k L i) hL.1 hL.2
  let e1 : FractionRing (L ⊗[k] field k i) ≃ₐ[L] FractionRing (L ⊗[k] tower k i) :=
    (CriticalTensorLocalization.fractionEquiv k L i hi h2).symm
  let e2 : FractionRing (L ⊗[k] tower k i) ≃ₐ[L] field L (algebraMap k L i) :=
    IsFractionRing.algEquivOfAlgEquiv (CriticalAffineBaseChange.towerEquiv i L)
  exact e1.trans e2

end FourCorner.CriticalConstantFieldComparison
#print axioms FourCorner.CriticalConstantFieldComparison.mapped_hypotheses
#print axioms FourCorner.CriticalConstantFieldComparison.fractionFieldEquiv
