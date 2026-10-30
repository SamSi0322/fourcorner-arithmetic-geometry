import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_FGSubalgebra
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_FGSubalgebra_nonempty_isColimit_cocone
import ThetaCoverClassPortable.P2M.Util
namespace P2MW.S_AlgebraicGeometry_FGSubalgebra_nonempty_isLimit_specCone

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem solution
    (R : Type u) [CommRing R] (A : Type u) [CommRing A] [Algebra R A] :
    Nonempty (IsLimit (FGSubalgebra.specCone R A)) :=
  ⟨isLimitOfPreserves Scheme.Spec (FGSubalgebra.nonempty_isColimit_cocone R A).some.op⟩
