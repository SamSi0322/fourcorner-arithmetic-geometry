import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase

noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
universe u
namespace AlgebraicGeometry.RelPicard.BaseChange
variable {R : Type u} [CommRing R] {C T T' : Scheme.{u}}
  (cc : C ⟶ Spec (.of R)) {t : T ⟶ Spec (.of R)} {t' : T' ⟶ Spec (.of R)}
  (ψ : SchemeHomOver t' t)

theorem baseChangeSnd_fst' :
    RelPicard.baseChangeSnd cc ψ ≫ pullback.fst cc t = pullback.fst cc t' :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

theorem baseChangeSnd_snd' :
    RelPicard.baseChangeSnd cc ψ ≫ pullback.snd cc t = pullback.snd cc t' ≫ ψ.1 :=
  pullback.lift_snd _ _ _
end AlgebraicGeometry.RelPicard.BaseChange
