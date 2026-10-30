import CriticalDoubleFieldMap
import CriticalSchemeIso

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
open AlgebraicGeometry CategoryTheory
universe u
namespace FourCorner.CriticalDoubleSchemeMap
variable {k : Type u} [Field k]

/-- The genuine generic-stalk endomorphism of the accepted independent E,
constructed from the explicit nonconstant CM function-field map. -/
def genericMap (i : k) (hi : i^2 = -1) (h2 : (2:k)≠0) :
    letI := EllipticQuarticModel.integral k
    letI := SmoothCurveExtension.fieldAlgebra (EllipticQuarticModel.toBase k)
    (EllipticQuarticModel.curve k).functionField →ₐ[k]
      (EllipticQuarticModel.curve k).functionField := by
  letI := EllipticQuarticModel.integral k
  letI := SmoothCurveExtension.fieldAlgebra (EllipticQuarticModel.toBase k)
  let e:=EllipticQuarticModel.nativeFieldEquiv k
  exact e.toAlgHom.comp ((CriticalDoubleFieldMap.map k i hi h2).comp e.symm.toAlgHom)

theorem exists_self_map (i : k) (hi : i^2 = -1) (h2 : (2:k)≠0) :
    letI := EllipticQuarticModel.integral k
    letI := SmoothCurveExtension.fieldAlgebra (EllipticQuarticModel.toBase k)
    ∃ π : EllipticQuarticModel.curve k ⟶ EllipticQuarticModel.curve k,
      π ≫ EllipticQuarticModel.toBase k=EllipticQuarticModel.toBase k ∧
      (EllipticQuarticModel.curve k).fromSpecStalk (genericPoint (EllipticQuarticModel.curve k)) ≫ π=
        Spec.map (CommRingCat.ofHom (genericMap i hi h2).toRingHom) ≫
          (EllipticQuarticModel.curve k).fromSpecStalk (genericPoint (EllipticQuarticModel.curve k)) := by
  letI := EllipticQuarticModel.integral k
  letI := EllipticQuarticModel.smooth k h2
  letI := EllipticQuarticModel.proper k
  letI := SmoothCurveExtension.fieldAlgebra (EllipticQuarticModel.toBase k)
  apply SmoothCurveExtension.extend_generic (EllipticQuarticModel.toBase k) (EllipticQuarticModel.toBase k)
    (Spec.map (CommRingCat.ofHom (genericMap i hi h2).toRingHom) ≫
      (EllipticQuarticModel.curve k).fromSpecStalk (genericPoint (EllipticQuarticModel.curve k)))
  simp only [Category.assoc,SmoothCurveExtension.generic_comp_to_base]
  rw [←Spec.map_comp,←CommRingCat.ofHom_comp]
  congr 1
  ext c
  exact (genericMap i hi h2).commutes c

/-- An actual proper-curve map to the ORIGINAL literal projective Ci.
Its further identification with the normalized product extension requires
the original product squareclass bridge; it is not assumed here. -/
theorem exists_original_map (i : k) (hi : i^2 = -1) (h2 : (2:k)≠0) :
    ∃ π : EllipticQuarticModel.curve k ⟶ CriticalProj23.criticalCurve i,
      π ≫ CriticalProj23.criticalToSpec i=EllipticQuarticModel.toBase k := by
  letI := EllipticQuarticModel.integral k
  obtain ⟨π,hπ,_⟩:=exists_self_map i hi h2
  let e:=CriticalSchemeIso.iso i hi h2
  have he : e.inv ≫ CriticalProj23.criticalToSpec i=EllipticQuarticModel.toBase k := by
    rw [←CriticalSchemeIso.iso_over_base i hi h2]
    exact e.inv_hom_id_assoc _
  exact ⟨π ≫ e.inv,by rw [Category.assoc,he,hπ]⟩

end FourCorner.CriticalDoubleSchemeMap
#print axioms FourCorner.CriticalDoubleSchemeMap.genericMap
#print axioms FourCorner.CriticalDoubleSchemeMap.exists_self_map
#print axioms FourCorner.CriticalDoubleSchemeMap.exists_original_map
