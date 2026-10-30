import ThetaCoverClassPortable.DUniversalGlobalSections
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_RelPicard_isSheafFor_relSubPicPresheaf_algEquivZeroCut_finite_faithfullyFlat_of_bijective_sections

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
  AlgebraicGeometry.SmoothProperCurve NeronModelInfra
namespace FourCorner.DRationalInputs

/-- Finite faithfully flat class descent for the literal D/QQ and OD.
Canonical global sections are supplied for every QQ-algebra, including the
zero ring and nonreduced algebras. -/
theorem actual_relSubPic_finiteFF_sheaf
    (A : Type) [CommRing A] [Algebra ℚ A] [Module.Finite ℚ A]
    [Module.FaithfullyFlat ℚ A] (T : Over (Spec (CommRingCat.of ℚ))) :
    Presieve.IsSheafFor (relSubPicPresheaf toBase OD (algEquivZeroCut toBase OD))
      (Presieve.singleton ((Over.mapPullbackAdj (specMap ℚ A)).counit.app T)) := by
  apply AlgebraicGeometry.RelPicard.isSheafFor_relSubPicPresheaf_algEquivZeroCut_finite_faithfullyFlat_of_bijective_sections
    ℚ toBase OD
  intro B _ _
  exact actual_universal_global_sections B

end FourCorner.DRationalInputs
