import HpTensorComparison
import CommonConstantTensorFraction
import CommonTensorCancelLeft
import Slot03HighTensorFraction
import TensorAlgebraicConstants
import FunctionFieldIntegralConstants

namespace FourCorner.HpConstantFieldComparison

open scoped TensorProduct
open HpLiteralField HpFieldGeometry AlgebraicCurve
noncomputable section
variable (K L : Type*) [Field K] [Field L] [NeZero (2 : K)] [NeZero (2 : L)] [Algebra K L]
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
local instance constantAlgebra (p : K) : Algebra K (field K p) := HpFieldGeometry.constantAlgebra K p
local instance constantModule (p : K) : Module K (field K p) := Algebra.toModule

/-- The fraction field of the actual constant tensor is the literal mapped
Hasse field. This proves the geometric-function-field comparison. -/
def fractionFieldEquiv (p : K) (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0) :
    letI := HpTensorComparison.all_constants_domain K L p hp ha hb
    FractionRing (L ⊗[K] (field K p)) ≃ₐ[L] field L (algebraMap K L p) := by
  letI := HpTensorComparison.all_constants_domain K L p hp ha hb
  let F := RatFunc K
  let G := RatFunc L
  let E := field K p
  letI : Algebra F E := inferInstanceAs (Algebra (RatFunc K) (field K p))
  letI : IsScalarTower K F E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let A := L ⊗[K] F
  letI := CommonFieldTensorDomain.ratAlgebra K L
  letI : Algebra F A := Algebra.TensorProduct.rightAlgebra
  let B := A ⊗[F] E
  let T := G ⊗[F] E
  letI : Algebra A G := CommonConstantTensorFraction.fractionAlgebra K L
  letI : IsScalarTower F A G := IsScalarTower.of_algebraMap_eq fun r => by
    change CommonConstantMap.ratMap K L r=CommonConstantTensorInjection.tensorMap K L (1 ⊗ₜ[K] r)
    simp only [CommonConstantTensorInjection.tensorMap,Algebra.TensorProduct.lift_tmul,map_one,one_mul]
    rfl
  letI : IsScalarTower L A G := IsScalarTower.of_algebraMap_eq fun l =>
    (CommonConstantTensorInjection.tensorMap K L).commutes l |>.symm
  letI : IsFractionRing A G := CommonConstantTensorFraction.isFractionRing K L
  haveI : IsDomain A := Function.Injective.isDomain (CommonConstantTensorInjection.tensorMap K L)
    (CommonConstantTensorInjection.tensorMap_injective K L)
  let eB : B ≃ₐ[L] L ⊗[K] E := CommonTensorCancelLeft.equiv K F L E
  letI : IsDomain B := Function.Injective.isDomain eB eB.injective
  letI : IsDomain T := HpTensorComparison.rational_tensor_domain K L p hp ha hb
  letI : Algebra B T := Slot03High.tensorAlgebra F A G E
  letI : Algebra L B := inferInstance
  letI : Algebra L T := inferInstance
  letI : IsScalarTower L B T := IsScalarTower.of_algebraMap_eq (R:=L) (S:=B) (A:=T) fun l => by
    change algebraMap L G l ⊗ₜ[F] (1 : E)=Slot03High.tensorMap F A G E ((l ⊗ₜ[K] (1 : F)) ⊗ₜ[F] (1 : E))
    simp only [Slot03High.tensorMap,Algebra.TensorProduct.map_tmul,AlgHom.id_apply,IsScalarTower.coe_toAlgHom]
    change algebraMap L G l ⊗ₜ[F] (1 : E)=CommonConstantTensorInjection.tensorMap K L (l ⊗ₜ[K] (1 : F)) ⊗ₜ[F] (1 : E)
    simp [CommonConstantTensorInjection.tensorMap,Algebra.TensorProduct.lift_tmul]
    rfl
  let S := Algebra.algebraMapSubmonoid B (nonZeroDivisors A)
  letI : IsLocalization S T := Slot03High.tensor_isLocalization F A G E
  have hS : S≤nonZeroDivisors B := by
    rintro _ ⟨a,ha,rfl⟩
    apply mem_nonZeroDivisors_of_ne_zero
    intro hz
    have hi := Algebra.TensorProduct.includeLeft_injective (R:=F) (S:=F) (A:=A) (B:=E) (algebraMap F E).injective
    exact nonZeroDivisors.ne_zero ha (hi (hz.trans (map_zero _).symm))
  let e1 : FractionRing (L ⊗[K] E) ≃ₐ[L] FractionRing B := IsFractionRing.algEquivOfAlgEquiv eB.symm
  let e2 : FractionRing B ≃ₐ[L] FractionRing T := Slot03High.fractionLocalizationEquiv L B T S hS
  let D := field L (algebraMap K L p)
  letI : Algebra G D := inferInstanceAs (Algebra (RatFunc L) D)
  letI : IsScalarTower L G D := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let e3 : T ≃ₐ[L] D := (HpTensorComparison.baseChangeEquiv K L p hp ha hb).restrictScalars L
  let e4 : FractionRing T ≃ₐ[L] FractionRing D := IsFractionRing.algEquivOfAlgEquiv e3
  let e5 : FractionRing D ≃ₐ[L] D := (FractionRing.algEquiv (A:=D) D).restrictScalars L
  exact e1.trans (e2.trans (e4.trans e5))

end

section FullConstants
open scoped TensorProduct
open HpLiteralField HpFieldGeometry AlgebraicCurve
variable (K : Type*) [Field K] [PerfectField K] [NeZero (2 : K)]
noncomputable section
local instance constantAlgebra' (p : K) : Algebra K (field K p) := HpFieldGeometry.constantAlgebra K p
local instance constantModule' (p : K) : Module K (field K p) := Algebra.toModule

/-- Full constants are proved from actual geometric tensor integrality,
independently of rational-place existence or a Hasse--Weil conclusion. -/
theorem constantsAreBase (p : K) (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0) : ConstantsAreBase K (field K p) := by
  let F := field K p
  letI := finite_over_line K p
  letI : NeZero (2 : AlgebraicClosure K) := ⟨by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap K (AlgebraicClosure K))).mpr (NeZero.ne (2 : K))⟩
  letI := HpTensorComparison.all_constants_domain K (AlgebraicClosure K) p hp ha hb
  change LSpace (0 : Divisor K F)=LinearMap.range (Algebra.linearMap K F)
  apply le_antisymm
  · intro x hx
    obtain ⟨c,hc⟩ := TensorAlgebraicConstants.integral_is_base (FunctionFieldIntegralConstants.lSpace_zero_integral K F hx)
    exact ⟨c,hc⟩
  · rintro x ⟨c,rfl⟩
    exact algebraMap_mem_lSpace_zero c

end
end FullConstants

#print axioms fractionFieldEquiv
#print axioms constantsAreBase

end FourCorner.HpConstantFieldComparison
