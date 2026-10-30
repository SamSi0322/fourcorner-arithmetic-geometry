import ThetaCoverClassPortable.DRationalInputs
import ThetaCoverClassPortable.FieldH0BaseChange

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourCorner.DRationalInputs
open AlgebraicGeometry AlgebraicCurve CategoryTheory CategoryTheory.Limits
local instance : IsIntegral curve := integral
local instance : IsProper toBase := proper
local instance : SmoothOfRelativeDimension 1 toBase := smooth
local instance : Algebra ℚ field := constants

/-- Every QQ-algebra, including nonreduced and zero rings, has exactly its
own scalars as global functions on the ACTUAL base change of original D. -/
theorem actual_universal_global_sections (A : Type) [CommRing A] [Algebra ℚ A] :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom
      (pullback.snd toBase (Scheme.TwoAffineOpenCover.specMap ℚ A)) ⊤
    Function.Bijective (algebraMap A Γ(pullback toBase (Scheme.TwoAffineOpenCover.specMap ℚ A),⊤)) :=
  Scheme.bijective_algebraMap_sections_baseChange_of_bijective_of_field
    ℚ toBase actual_global_sections_bijective A

end FourCorner.DRationalInputs
