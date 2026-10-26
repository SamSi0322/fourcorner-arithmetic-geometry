import EllipticQuarticIntegral
import AffineGenericStalk

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
universe u
namespace FourCorner.EllipticQuarticModel
variable (K : Type u) [Field K]

def nativeChart : Spec (.of (CriticalEllipticField.ring K)) ⟶ curve K :=
  (zeroNativeIso K).inv ≫ (Proj.basicOpen (grading K) (projectiveCoordinate K 0)).ι

instance nativeChart_isOpenImmersion : IsOpenImmersion (nativeChart K) := by
  unfold nativeChart
  infer_instance

theorem nativeChart_over_base : nativeChart K ≫ toBase K =
    Spec.map (CommRingCat.ofHom (algebraMap K (CriticalEllipticField.ring K))) := by
  change (Spec.map (CommRingCat.ofHom (affineEquiv K).toRingEquiv.toRingHom) ≫
    (chartIso K 0).inv ≫ (Proj.basicOpen (grading K) (projectiveCoordinate K 0)).ι) ≫ toBase K = _
  simp only [Category.assoc]
  rw [chart_over_base,←Spec.map_comp,←CommRingCat.ofHom_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  ext a
  exact (affineEquiv K).commutes a

local instance targetIntegral : IsIntegral (curve K) := integral K

/-- The independently constructed projective target has exactly the native
Weierstrass function field; the equivalence uses its actual open chart stalk. -/
def nativeFieldEquiv :
    letI := SmoothCurveExtension.fieldAlgebra (toBase K);
    CriticalEllipticField.field K ≃ₐ[K] (curve K).functionField :=
  AffineGenericStalk.fieldEquiv (toBase K) (nativeChart K) (nativeChart_over_base K)

theorem native_generic_diagram :
    Spec.map (CommRingCat.ofHom (AffineGenericStalk.ringEquiv (nativeChart K)).toRingHom) ≫
      (curve K).fromSpecStalk (genericPoint (curve K)) =
      (Spec (.of (CriticalEllipticField.ring K))).fromSpecStalk
        (genericPoint (Spec (.of (CriticalEllipticField.ring K)))) ≫ nativeChart K :=
  AffineGenericStalk.generic_diagram (nativeChart K)

end FourCorner.EllipticQuarticModel
#print axioms FourCorner.EllipticQuarticModel.nativeChart_over_base
#print axioms FourCorner.EllipticQuarticModel.nativeFieldEquiv
#print axioms FourCorner.EllipticQuarticModel.native_generic_diagram
