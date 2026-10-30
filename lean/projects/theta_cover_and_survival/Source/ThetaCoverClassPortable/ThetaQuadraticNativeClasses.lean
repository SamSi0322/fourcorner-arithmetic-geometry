import ThetaCoverClassPortable.ThetaQuadraticInfinityScheme
import ThetaCoverClassPortable.ThetaQuadraticContactBaseChange

noncomputable section
set_option autoImplicit false
open AlgebraicGeometry AlgebraicCurve

namespace FourCorner.ThetaQuadraticNativeClasses
open ThetaQuadraticCurve ThetaQuadraticBoundary ThetaQuadraticInfinityScheme
local instance : IsIntegral curve := curve_integral
local instance : Algebra F functionField := ThetaQuadraticCurve.fieldAlgebra

/-- Degree zero follows from the genuine residue-field degrees of the
actual four boundary points and the actual two quadratic infinity points. -/
def boundaryDifference : Divisor.degZero (K:=F) (F:=functionField) :=
  ⟨E2-H2,by rw [Divisor.mem_degZero,map_sub,E2_degree,H2_degree];norm_num⟩

/-- Native Pic0 of the actual F-curve's actual function field. No represented
Jacobian or unproved scalar-extension identification is part of this definition. -/
def delta2 : Pic0 F functionField := Pic0.mk boundaryDifference

abbrev contactClass := ThetaQuadraticContactPlaces.contactClass

end FourCorner.ThetaQuadraticNativeClasses
