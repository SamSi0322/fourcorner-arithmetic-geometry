import ThetaCoverClassPortable.FieldH0BaseChange
import ThetaCoverClassPortable.ThetaGlobalSectionsConstant

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FourCorner.ThetaRationalPicardInput
open AlgebraicGeometry AlgebraicCurve CategoryTheory CategoryTheory.Limits
open ThetaLiteralModels
attribute [local instance] sourceIntegral sourceSmooth sourceProper constants

/-- For EVERY Q-algebra A, including the zero ring, global functions on
the ACTUAL A-base change of the original theta curve are exactly A. -/
theorem actual_universal_global_sections (A : Type) [CommRing A] [Algebra ℚ A] :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom
      (pullback.snd (cToBase ℚ) (Scheme.TwoAffineOpenCover.specMap ℚ A)) ⊤
    Function.Bijective (algebraMap A
      Γ(pullback (cToBase ℚ) (Scheme.TwoAffineOpenCover.specMap ℚ A), ⊤)) :=
  Scheme.bijective_algebraMap_sections_baseChange_of_bijective_of_field
    ℚ (cToBase ℚ) actual_global_sections_bijective A

#check @actual_universal_global_sections
#print axioms actual_universal_global_sections
end FourCorner.ThetaRationalPicardInput
