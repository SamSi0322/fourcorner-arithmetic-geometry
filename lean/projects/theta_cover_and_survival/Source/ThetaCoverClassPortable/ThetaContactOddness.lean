import ThetaCoverClassPortable.ThetaVerticalContactConstants
import ThetaCoverClassPortable.PicEllOneOfConstants

namespace FourCorner.ThetaContactOddness
open AlgebraicGeometry AlgebraicCurve CategoryTheory
open ThetaDGeometricModel ThetaActualLineDifferentials ThetaActualHalfCanonicalContacts
open ThetaAffineContactConstants ThetaVerticalContactConstants DivisorPicClassification
noncomputable section
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
local instance : IsIntegral geometricD := geometric_integral
local instance : IsProper toBase := geometric_proper
local instance : SmoothOfRelativeDimension 1 toBase := geometric_smooth
local instance : Algebra K field := fieldAlgebra
local instance : IsCurveOver K field := field_isCurveOver
local instance : Algebra.EssFiniteType K field := field_essFiniteType
local instance : HasCanonicalDivisor (K:=K) (F:=field) := hasCanonicalDivisor_of_isCurveOver
local instance : ∀w : Place K field,w.DCoordGenerates := dCoordGenerates_of_isCurveOver
local instance : Module K Γ(toBase.kaehler,⊤) :=
  Scheme.TwoAffineOpenCover.moduleSectionsOfHom toBase toBase.kaehler ⊤

 theorem affine_contact_ell_one (α β : K) (h : IsThetaSquareContact (.affine α β))
    (data : ContactData (affineGlobalSection α β)) : ell data.divisor=1 :=
  ell_eq_one_of_constant_sections _ data.effective (affine_contact_constants α β h data)

 theorem vertical_contact_ell_one (t : K) (h : IsThetaSquareContact (.vertical t))
    (data : ContactData (verticalGlobalSection t)) : ell data.divisor=1 :=
  ell_eq_one_of_constant_sections _ data.effective (vertical_contact_constants t h data)

/-- Actual native divisor-Pic oddness is proved, not assumed from the 28-line
labels or from a replacement Pic/Galois set. Scheme linebundle/Pic and the
full converse remain separate explicit assembly obligations. -/
theorem affine_contact_odd (α β : K) (h : IsThetaSquareContact (.affine α β))
    (data : ContactData (affineGlobalSection α β)) : IsOddThetaClass (divisorClass data.divisor) :=
  isOddThetaClass_of_constant_sections _ data.effective data.germ_ne_zero data.doubled_divisor
    (affine_contact_constants α β h data)

 theorem vertical_contact_odd (t : K) (h : IsThetaSquareContact (.vertical t))
    (data : ContactData (verticalGlobalSection t)) : IsOddThetaClass (divisorClass data.divisor) :=
  isOddThetaClass_of_constant_sections _ data.effective data.germ_ne_zero data.doubled_divisor
    (vertical_contact_constants t h data)

#print axioms affine_contact_ell_one
#print axioms vertical_contact_ell_one
#print axioms affine_contact_odd
#print axioms vertical_contact_odd
end
end FourCorner.ThetaContactOddness
