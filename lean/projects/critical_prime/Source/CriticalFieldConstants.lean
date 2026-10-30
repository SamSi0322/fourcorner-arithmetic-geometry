import CriticalRadicalField
import FractionTensorDomain
import TensorAlgebraicConstants
import FunctionFieldIntegralConstants

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 400000
open Polynomial AlgebraicCurve
open scoped TensorProduct
namespace FourCorner.CriticalFieldConstants
open CriticalRadicalField
variable (k : Type*) [Field k]

/-- The original constant-field action, fixed before introducing the
coordinate and polynomial scalar towers. -/
local instance constantAlgebra (i : k) : Algebra k (field k i) :=
  IntermediateField.algebra' (R':=k) (field k i)
local instance constantModule (i : k) : Module k (field k i) :=
  (constantAlgebra k i).toModule

/-- The fixed action has exactly the original constant embedding through
k[X] and k(X), as used by the frozen literal radical coordinates. -/
theorem constant_embedding (i z : k) :
    algebraMap k (field k i) z = CriticalRadicalField.polynomialValue k i (Polynomial.C z) :=
  (CriticalRadicalField.polynomialValue_C k i z).symm

theorem constant_smul (i : k) (z : k) (x : field k i) :
    z • x = CriticalRadicalField.polynomialValue k i (Polynomial.C z) * x := by
  rw [Algebra.smul_def,constant_embedding]

local instance polynomialFieldAlgebra (i : k) : Algebra k[X] (field k i) :=
  IntermediateField.algebra' (R':=k[X]) (field k i)
local instance polynomial_line_field (i : k) : IsScalarTower k[X] (RatFunc k) (field k i) :=
  Biquadratic.CoordinateAlgebra.targetScalarTower k[X] (RatFunc k)
    (CriticalSquareclasses.qB i) (CriticalSquareclasses.qC i)
local instance towerFieldAlgebra (i : k) : Algebra (tower k i) (field k i) :=
  Biquadratic.CoordinateAlgebra.coordinateAlgebra k[X] (RatFunc k)
    (CriticalSquareclasses.qB i) (CriticalSquareclasses.qC i)
local instance polynomial_tower_field (i : k) : IsScalarTower k[X] (tower k i) (field k i) :=
  Biquadratic.CoordinateAlgebra.coordinateScalarTower k[X] (RatFunc k)
    (CriticalSquareclasses.qB i) (CriticalSquareclasses.qC i)
local instance constants_tower_field (i : k) : IsScalarTower k (tower k i) (field k i) := by
  haveI : IsScalarTower k k[X] (field k i) :=
    IsScalarTower.to₁₂₄ k k[X] (RatFunc k) (field k i)
  exact IsScalarTower.to₁₃₄ k k[X] (tower k i) (field k i)

theorem tower_domain (i : k) (hi : i^2 = -1) (h2 : (2:k)≠0) : IsDomain (tower k i) := by
  letI := CriticalAffineDomain.ring_isDomain i hi h2
  exact Function.Injective.isDomain (CriticalAffineTower.equiv i).symm.toRingHom
    (CriticalAffineTower.equiv i).symm.injective

theorem tower_fraction (i : k) (hi : i^2 = -1) (h2 : (2:k)≠0) :
    IsFractionRing (tower k i) (field k i) := by
  have h2F : (2:RatFunc k)≠0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap k (RatFunc k))).mpr h2
  exact Biquadratic.CoordinateAlgebra.isFractionRing_coordinateRing k[X] (RatFunc k)
    (CriticalSquareclasses.qB i) (CriticalSquareclasses.qC i) h2F
    (CriticalSquareclasses.independent i hi h2)

theorem tower_tensor_domain (i : k) (hi : i^2 = -1) (h2 : (2:k)≠0)
    (L : Type*) [Field L] [Algebra k L] : IsDomain (L ⊗[k] tower k i) := by
  letI := CriticalAffineBaseChange.isDomain_tensor i L hi h2
  let e := Algebra.TensorProduct.congr (AlgEquiv.refl : L ≃ₐ[k] L)
    (CriticalAffineTower.equiv i).symm
  exact Function.Injective.isDomain e.toRingHom e.injective


/-- The actual two-root function field remains a domain after EVERY extension
of constants, through its literal coordinate algebra and true localization. -/
theorem field_tensor_domain (i : k) (hi : i^2 = -1) (h2 : (2:k)≠0)
    (L : Type*) [Field L] [Algebra k L] : IsDomain (L ⊗[k] field k i) := by
  letI := tower_domain k i hi h2
  letI := tower_fraction k i hi h2
  letI := tower_tensor_domain k i hi h2 L
  exact FractionTensorDomain.tensor_isDomain k L (tower k i) (field k i)

/-- Full constants of the literal critical function field are proved without
assuming a rational place, a Hasse bound, or a supplied genus value. -/
theorem constantsAreBase [PerfectField k] (i : k) (hi : i^2 = -1) (h2 : (2:k)≠0) :
    AlgebraicCurve.ConstantsAreBase k (field k i) := by
  letI := field_tensor_domain k i hi h2 (AlgebraicClosure k)
  change LSpace (0 : Divisor k (field k i)) = LinearMap.range (Algebra.linearMap k (field k i))
  apply le_antisymm
  · intro x hx
    obtain ⟨z,hz⟩ := TensorAlgebraicConstants.integral_is_base
      (FunctionFieldIntegralConstants.lSpace_zero_integral k (field k i) hx)
    exact ⟨z,hz⟩
  · rintro x ⟨z,rfl⟩
    exact algebraMap_mem_lSpace_zero z

end FourCorner.CriticalFieldConstants
#print axioms FourCorner.CriticalFieldConstants.constant_embedding
#print axioms FourCorner.CriticalFieldConstants.constant_smul
#print axioms FourCorner.CriticalFieldConstants.tower_fraction
#print axioms FourCorner.CriticalFieldConstants.field_tensor_domain
#print axioms FourCorner.CriticalFieldConstants.constantsAreBase
