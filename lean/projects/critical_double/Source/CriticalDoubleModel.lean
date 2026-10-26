import CriticalDoubleFieldIso
import CriticalDoubleSchemeMap
import CriticalGeometricConnected

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
open AlgebraicGeometry CategoryTheory
universe u
namespace FourCorner.CriticalDoubleModel
variable {k : Type u} [Field k]
local instance coverConstants (i:k) : Algebra k (CriticalLiteralDouble.field k i) := CriticalLiteralDouble.targetConstants k i
local instance coverModule (i:k) : Module k (CriticalLiteralDouble.field k i) := (coverConstants i).toModule

/-- A genuine proper smooth model of the EXACT original product-root field.
The field equivalence comes with the proved original base/root formula. -/
def fieldEquiv (i:k) (hi:i^2 = -1) (h2:(2:k)≠0) :
    letI := EllipticQuarticModel.integral k
    letI := SmoothCurveExtension.fieldAlgebra (EllipticQuarticModel.toBase k)
    CriticalLiteralDouble.field k i ≃ₐ[k] (EllipticQuarticModel.curve k).functionField := by
  letI := EllipticQuarticModel.integral k
  letI := SmoothCurveExtension.fieldAlgebra (EllipticQuarticModel.toBase k)
  exact (CriticalDoubleFieldIso.equiv k i hi h2).trans (EllipticQuarticModel.nativeFieldEquiv k)

theorem geometricallyConnected (i:k) (hi:i^2 = -1) (h2:(2:k)≠0) :
    GeometricallyConnected (EllipticQuarticModel.toBase k) := by
  let e:=CriticalSchemeIso.iso i hi h2
  have hc:GeometricallyConnected (e.hom ≫ EllipticQuarticModel.toBase k) := by
    rw [CriticalSchemeIso.iso_over_base i hi h2]
    exact CriticalGeometricConnected.geometricallyConnected i hi h2
  exact (MorphismProperty.cancel_left_of_respectsIso @GeometricallyConnected e.hom
    (EllipticQuarticModel.toBase k)).mp hc

def rationalPoint : Spec (.of k) ⟶ EllipticQuarticModel.curve k :=
  Spec.map (CommRingCat.ofHom (CriticalEllipticField.evaluate k 1 0 (by ring)).toRingHom) ≫
    EllipticQuarticModel.nativeChart k

theorem rationalPoint_over : (rationalPoint (k:=k)) ≫ EllipticQuarticModel.toBase k=𝟙 _ := by
  rw [rationalPoint,Category.assoc,EllipticQuarticModel.nativeChart_over_base,←Spec.map_comp]
  change Spec.map (CommRingCat.ofHom
    ((CriticalEllipticField.evaluate k 1 0 (by ring)).toRingHom.comp
      (algebraMap k (CriticalEllipticField.ring k))))=𝟙 _
  have hc : (CriticalEllipticField.evaluate k 1 0 (by ring)).toRingHom.comp
      (algebraMap k (CriticalEllipticField.ring k))=RingHom.id k := by
    ext z
    exact (CriticalEllipticField.evaluate k 1 0 (by ring)).commutes z
  rw [hc]
  simp only [CommRingCat.ofHom_id,Spec.map_id]

end FourCorner.CriticalDoubleModel
#print axioms FourCorner.CriticalDoubleModel.fieldEquiv
#print axioms FourCorner.CriticalDoubleModel.geometricallyConnected
#print axioms FourCorner.CriticalDoubleModel.rationalPoint_over
