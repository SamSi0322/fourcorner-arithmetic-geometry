import ThetaCoverClassPortable.NativeCurveGlobalConstants
import ThetaCoverClassPortable.ThetaRationalRiemannBound

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FourCorner.ThetaRationalPicardInput
open AlgebraicGeometry AlgebraicCurve CategoryTheory
open ThetaLiteralModels
attribute [local instance] sourceIntegral sourceSmooth sourceProper constants

/-- The actual structural map from Q to global functions on the original
theta curve is bijective, without a representability or base-change premise. -/
theorem actual_global_sections_bijective :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom (cToBase ℚ) ⊤
    Function.Bijective (algebraMap ℚ Γ(C ℚ, ⊤)) :=
  NativeCurveGlobalConstants.global_sections_bijective (cToBase ℚ) source_constantsAreBase

#print axioms actual_global_sections_bijective
end FourCorner.ThetaRationalPicardInput
