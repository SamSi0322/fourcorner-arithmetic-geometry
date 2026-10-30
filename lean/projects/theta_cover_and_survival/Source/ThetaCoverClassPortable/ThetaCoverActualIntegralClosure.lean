import ThetaCoverClassPortable.SmoothCurveAffineNormal
import ThetaCoverClassPortable.ThetaSourceSmooth
import ThetaCoverClassPortable.ThetaSourceComparison
import ThetaCoverClassPortable.ThetaProjectionDegree

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry AlgebraicCurve CategoryTheory
namespace FourCorner.ThetaCoverActualIntegralClosure
open ThetaLiteralModels SmoothCurveAffineNormal
abbrev pi := ThetaProjection.projection (k:=ℚ)
local instance : IsIntegral (C ℚ) := ThetaSourceComparison.source_integral
local instance : SmoothOfRelativeDimension 1 (cToBase ℚ) := ThetaSourceSmooth.source_smooth
local instance : IsFinite pi := ThetaProjectionFiniteEtale.projection_finite
local instance : Surjective pi := ThetaProjectionDegree.projection_surjective

 theorem preimage_nonempty (U : (D ℚ).Opens) [Nonempty U] : Nonempty (pi ⁻¹ᵁ U) := by
  obtain ⟨y⟩ := (inferInstance : Nonempty U)
  obtain ⟨x,hx⟩ := pi.surjective y.val
  exact ⟨⟨x,by change pi x∈U;rw [hx];exact y.property⟩⟩
local instance (U : (D ℚ).Opens) [Nonempty U] : Nonempty (pi ⁻¹ᵁ U) := preimage_nonempty U

@[instance_reducible] def affineSectionsAlgebra (U : (D ℚ).Opens) :
    Algebra Γ(D ℚ,U) Γ(C ℚ,pi ⁻¹ᵁ U) := (pi.app U).hom.toAlgebra
@[instance_reducible] def affineFieldAlgebra (U : (D ℚ).Opens) [Nonempty U] :
    Algebra Γ(D ℚ,U) (C ℚ).functionField :=
  ((algebraMap Γ(C ℚ,pi ⁻¹ᵁ U) (C ℚ).functionField).comp (pi.app U).hom).toAlgebra

/-- Full actual affine integral-closure assertion for the ORIGINAL finite
cover. Both finiteness/integrality and normality are derived internally;
there is no normalization/normality/IC input premise. The ambient field is
the actual original source generic stalk, with the actual induced maps. -/
theorem actual_affine_integralClosure (U : (D ℚ).Opens) (hU : IsAffineOpen U) [Nonempty U] :
    letI := affineSectionsAlgebra U
    letI := affineFieldAlgebra U
    IsIntegralClosure Γ(C ℚ,pi ⁻¹ᵁ U) Γ(D ℚ,U) (C ℚ).functionField := by
  letI := affineSectionsAlgebra U
  letI := affineFieldAlgebra U
  letI : IsScalarTower Γ(D ℚ,U) Γ(C ℚ,pi ⁻¹ᵁ U) (C ℚ).functionField :=
    IsScalarTower.of_algebraMap_eq (fun _=>rfl)
  letI : Module.Finite Γ(D ℚ,U) Γ(C ℚ,pi ⁻¹ᵁ U) := pi.finite_app U hU
  letI : IsIntegrallyClosed Γ(C ℚ,pi ⁻¹ᵁ U) :=
    affine_integrallyClosed (cToBase ℚ) _ (hU.preimage pi)
  letI : IsFractionRing Γ(C ℚ,pi ⁻¹ᵁ U) (C ℚ).functionField :=
    functionField_isFractionRing_of_isAffineOpen (C ℚ) _ (hU.preimage pi)
  infer_instance

#print axioms actual_affine_integralClosure
end FourCorner.ThetaCoverActualIntegralClosure
