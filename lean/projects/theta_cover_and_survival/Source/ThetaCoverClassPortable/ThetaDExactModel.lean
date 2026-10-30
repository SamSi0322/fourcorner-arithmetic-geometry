import ThetaCoverClassPortable.ThetaDNativeSections

namespace FourCorner.ThetaDExactModel
open AlgebraicGeometry CategoryTheory AlgebraicCurve ThetaDGeometricModel
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
local instance : IsIntegral geometricD := geometric_integral
local instance : SmoothOfRelativeDimension 1 toBase := geometric_smooth
local instance : IsProper toBase := geometric_proper

/-- Exact native model comparison, including the ACTUAL generic-point field
diagram. Neither a model nor a field/scheme comparison is postulated. -/
theorem exists_exact_model :
    letI := fieldAlgebra
    ∃M : CurveModel K geometricD.functionField,∃i : geometricD ≅ M.C,
      i.hom ≫ M.toBase=toBase ∧
      geometricD.fromSpecStalk (genericPoint geometricD) ≫ i.hom=
        Spec.map (CommRingCat.ofHom M.ffEquiv.symm.toRingHom) ≫
          M.C.fromSpecStalk (genericPoint M.C) :=
  NativeCurveModelExistence.exists_model toBase

#print axioms exists_exact_model
end
end FourCorner.ThetaDExactModel
