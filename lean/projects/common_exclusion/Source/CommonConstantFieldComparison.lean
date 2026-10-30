import CommonRootFieldComparison
import CommonConstantTensorFraction
import CommonTensorCancelLeft
import CommonGeometricField
import Slot03HighTensorFraction

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
namespace FourCorner.CommonConstantFieldComparison
open scoped TensorProduct
variable (K L : Type*) [Field K] [Field L] [CharZero K] [CharZero L] [Algebra K L]
local instance constantAlgebra (t : K) : Algebra K (CommonLiteralField.field K t) :=
  (CommonLiteralField.field K t).algebra'
local instance constantModule (t : K) : Module K (CommonLiteralField.field K t) := Algebra.toModule

/-- The fraction field of the ACTUAL constant tensor product is the literal
four-root field with mapped constants. This is the required function-field
comparison for the base change of the rational proper model. -/
def fractionFieldEquiv {t : K} (ht0 : t ≠ 0) (ht1 : t ≠ 1) (htm : t ≠ -1) :
    letI := CommonGeometricField.all_constants_domain K L ht0 ht1 htm
    FractionRing (L ⊗[K] (CommonLiteralField.field K t)) ≃ₐ[L]
      CommonLiteralField.field L (algebraMap K L t) := by
  letI := CommonGeometricField.all_constants_domain K L ht0 ht1 htm
  let F := RatFunc K
  let G := RatFunc L
  let E := CommonLiteralField.field K t
  letI : Algebra F E := inferInstanceAs (Algebra (RatFunc K) (CommonLiteralField.field K t).toSubalgebra)
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
  letI : IsDomain T := CommonFieldTensorDomain.isDomain_rationalFunction_baseChange K L ht0 ht1 htm
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
  let D := CommonLiteralField.field L (algebraMap K L t)
  letI : Algebra G D := inferInstanceAs (Algebra (RatFunc L) D.toSubalgebra)
  letI : Algebra L D := D.algebra'
  letI : IsScalarTower L G D := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let e3 : T ≃ₐ[L] CommonLiteralField.field L (algebraMap K L t) :=
    (CommonRootFieldComparison.baseChangeEquiv K L ht0 ht1 htm).restrictScalars L
  let e4 : FractionRing T ≃ₐ[L] FractionRing (CommonLiteralField.field L (algebraMap K L t)) :=
    IsFractionRing.algEquivOfAlgEquiv e3
  let e5 : FractionRing (CommonLiteralField.field L (algebraMap K L t)) ≃ₐ[L]
      CommonLiteralField.field L (algebraMap K L t) :=
    (FractionRing.algEquiv (A:=D) D).restrictScalars L
  exact e1.trans (e2.trans (e4.trans e5))

#print axioms fractionFieldEquiv
end FourCorner.CommonConstantFieldComparison
