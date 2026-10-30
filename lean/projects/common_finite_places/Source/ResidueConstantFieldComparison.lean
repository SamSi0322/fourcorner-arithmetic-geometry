import ResidueTensorComparison
import CommonConstantTensorFraction
import CommonTensorCancelLeft
import ResidueGeometricField
import Slot03HighTensorFraction

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
namespace FourCorner.ResidueConstantFieldComparison
open scoped TensorProduct
variable (K L : Type*) [Field K] [Field L] [NeZero (2 : K)] [NeZero (2 : L)] [Algebra K L]
open Genus17Geometry
local instance constantAlgebra (t κ : K) : Algebra K (field t κ) := modelFieldAlgebra t κ
local instance constantModule (t κ : K) : Module K (field t κ) := Algebra.toModule
/-- The fraction field of the ACTUAL constant tensor product is the literal
five-root field with mapped constants. This is the required function-field
comparison for the base change of the rational proper model. -/
def fractionFieldEquiv {t κ : K} (ht0 : t ≠ 0) (ht1 : t ≠ 1) (htm : t ≠ -1) (hκ : κ ≠ 0) :
    letI := ResidueGeometricField.all_constants_domain K L ht0 ht1 htm hκ
    FractionRing (L ⊗[K] (Genus17Geometry.field t κ)) ≃ₐ[L]
      Genus17Geometry.field (algebraMap K L t) (algebraMap K L κ) := by
  letI := ResidueGeometricField.all_constants_domain K L ht0 ht1 htm hκ
  let F := RatFunc K
  let G := RatFunc L
  let E := Genus17Geometry.field t κ
  letI : Algebra F E := inferInstanceAs (Algebra (RatFunc K) (Genus17Geometry.field t κ))
  letI : IsScalarTower K F E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let A := L ⊗[K] F
  letI := CommonFieldTensorDomain.ratAlgebra K L
  letI : Algebra F A := Algebra.TensorProduct.rightAlgebra
  let B := A ⊗[F] E
  let T := G ⊗[F] E
  letI : Algebra A G := CommonConstantTensorFraction.fractionAlgebra K L
  letI : IsScalarTower F A G := IsScalarTower.of_algebraMap_eq fun r => by
    change CommonConstantMap.ratMap K L r =
      CommonConstantTensorInjection.tensorMap K L (1 ⊗ₜ[K] r)
    simp only [CommonConstantTensorInjection.tensorMap,Algebra.TensorProduct.lift_tmul,
      map_one,one_mul]
    rfl
  letI : IsScalarTower L A G := IsScalarTower.of_algebraMap_eq fun l =>
    (CommonConstantTensorInjection.tensorMap K L).commutes l |>.symm
  letI : IsFractionRing A G := CommonConstantTensorFraction.isFractionRing K L
  haveI : IsDomain A := Function.Injective.isDomain
    (CommonConstantTensorInjection.tensorMap K L)
    (CommonConstantTensorInjection.tensorMap_injective K L)
  let eB : B ≃ₐ[L] L ⊗[K] E := CommonTensorCancelLeft.equiv K F L E
  letI : IsDomain B := Function.Injective.isDomain eB eB.injective
  letI : IsDomain T := ResidueTensorComparison.rational_tensor_domain K L ht0 ht1 htm hκ
  letI : Algebra B T := Slot03High.tensorAlgebra F A G E
  letI : Algebra L B := inferInstance
  letI : Algebra L T := inferInstance
  letI : IsScalarTower L B T := IsScalarTower.of_algebraMap_eq (R:=L) (S:=B) (A:=T) fun l => by
    change algebraMap L G l ⊗ₜ[F] (1:E) =
      Slot03High.tensorMap F A G E ((l ⊗ₜ[K] (1:F)) ⊗ₜ[F] (1:E))
    simp only [Slot03High.tensorMap,Algebra.TensorProduct.map_tmul,AlgHom.id_apply,
      IsScalarTower.coe_toAlgHom]
    change algebraMap L G l ⊗ₜ[F] (1:E) =
      CommonConstantTensorInjection.tensorMap K L (l ⊗ₜ[K] (1:F)) ⊗ₜ[F] (1:E)
    simp [CommonConstantTensorInjection.tensorMap,Algebra.TensorProduct.lift_tmul]
    rfl
  let S := Algebra.algebraMapSubmonoid B (nonZeroDivisors A)
  letI : IsLocalization S T := Slot03High.tensor_isLocalization F A G E
  have hS : S ≤ nonZeroDivisors B := by
    rintro _ ⟨a,ha,rfl⟩
    apply mem_nonZeroDivisors_of_ne_zero
    intro hz
    have hi := Algebra.TensorProduct.includeLeft_injective
      (R:=F) (S:=F) (A:=A) (B:=E) (algebraMap F E).injective
    exact nonZeroDivisors.ne_zero ha (hi (hz.trans (map_zero _).symm))
  let e1 : FractionRing (L ⊗[K] E) ≃ₐ[L] FractionRing B :=
    IsFractionRing.algEquivOfAlgEquiv eB.symm
  let e2 : FractionRing B ≃ₐ[L] FractionRing T :=
    Slot03High.fractionLocalizationEquiv L B T S hS
  let D := Genus17Geometry.field (algebraMap K L t) (algebraMap K L κ)
  letI : Algebra G D := inferInstanceAs (Algebra (RatFunc L) D)
  letI : IsScalarTower L G D := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let e3 : T ≃ₐ[L] Genus17Geometry.field (algebraMap K L t) (algebraMap K L κ) :=
    (ResidueTensorComparison.baseChangeEquiv K L ht0 ht1 htm hκ).restrictScalars L
  let e4 : FractionRing T ≃ₐ[L] FractionRing (Genus17Geometry.field (algebraMap K L t) (algebraMap K L κ)) :=
    IsFractionRing.algEquivOfAlgEquiv e3
  let e5 : FractionRing (Genus17Geometry.field (algebraMap K L t) (algebraMap K L κ)) ≃ₐ[L]
      Genus17Geometry.field (algebraMap K L t) (algebraMap K L κ) :=
    (FractionRing.algEquiv (A:=D) D).restrictScalars L
  exact e1.trans (e2.trans (e4.trans e5))

#print axioms fractionFieldEquiv
end FourCorner.ResidueConstantFieldComparison
