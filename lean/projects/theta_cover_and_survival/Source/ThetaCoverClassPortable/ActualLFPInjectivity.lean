import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_RelPicard_isLFPInj_relPicardPresheaf
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_RelPicard_isLFPInj_relSubPicPresheaf_algEquivZeroCut

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra
namespace FourCorner.ActualLFPInjectivity

/-- Finite-stage injectivity for the actual raw Picard presheaf; no Noetherian premise. -/
theorem relPicard_of_twoAffineOpenCover
    (R : Type u) [CommRing R] {C : Scheme.{u}} (𝒱 : C.TwoAffineOpenCover)
    (c : C ⟶ Spec (CommRingCat.of R)) (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) :
    AffineLimit.IsLFPInj (relPicardPresheaf c ε) :=
  AlgebraicGeometry.RelPicard.isLFPInj_relPicardPresheaf R 𝒱 c ε

/-- The same genuine injectivity applies to every actual sub-Picard condition. -/
theorem relSubPicard_of_twoAffineOpenCover
    (R : Type u) [CommRing R] {C : Scheme.{u}} (𝒱 : C.TwoAffineOpenCover)
    (c : C ⟶ Spec (CommRingCat.of R)) (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (P : SubPicCondition c ε) : AffineLimit.IsLFPInj (relSubPicPresheaf c ε P) :=
  P2MW.S_AlgebraicGeometry_RelPicard_isLFPInj_relSubPicPresheaf_algEquivZeroCut.AlgebraicGeometry.RelPicard.isLFPInj_relSubPicPresheaf_of_relPicardPresheaf
    c ε P (relPicard_of_twoAffineOpenCover R 𝒱 c ε)

/-- In particular the algebraic-equivalence-zero cut needs no Noetherian premise once a cover is given. -/
theorem algEquivZeroCut_of_twoAffineOpenCover
    (R : Type u) [CommRing R] {C : Scheme.{u}} (𝒱 : C.TwoAffineOpenCover)
    (c : C ⟶ Spec (CommRingCat.of R)) (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) :
    AffineLimit.IsLFPInj (relSubPicPresheaf c ε (algEquivZeroCut c ε)) :=
  relSubPicard_of_twoAffineOpenCover R 𝒱 c ε (algEquivZeroCut c ε)

end FourCorner.ActualLFPInjectivity
