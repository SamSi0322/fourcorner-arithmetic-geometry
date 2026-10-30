import ThetaCoverClassPortable.ActualInfinitesimalPoints

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory
namespace FourCorner.ThetaLocalSurvival.Infinitesimal

variable (A R : Type) [CommRing A] [CommRing R] [Algebra ℚ A] [Algebra ℚ R]

def pointToAlgHom (P : pointObject R ⟶ pointObject A) : A →ₐ[ℚ] R :=
  { (Spec.preimage P.left).hom with
    commutes' := by
      intro q
      have hp := P.w
      rw [←Spec.map_preimage P.left] at hp
      change Spec.map (Spec.preimage P.left) ≫ Spec.map (CommRingCat.ofHom (algebraMap ℚ A))=
        Spec.map (CommRingCat.ofHom (algebraMap ℚ R)) at hp
      rw [←Spec.map_comp] at hp
      have h := Spec.map_injective hp
      exact congrArg (fun f : CommRingCat.of ℚ ⟶ .of R => f.hom q) h }

theorem pointChange_pointToAlgHom (P : pointObject R ⟶ pointObject A) :
    pointChange (pointToAlgHom A R P)=P := by
  apply Over.OverMorphism.ext
  exact Spec.map_preimage P.left

theorem pointToAlgHom_pointChange (f : A →ₐ[ℚ] R) :
    pointToAlgHom A R (pointChange f)=f := by
  apply AlgHom.ext
  intro a
  have h := Spec.homEquiv.apply_symm_apply (CommRingCat.ofHom f.toRingHom)
  exact congrArg (fun g : CommRingCat.of A ⟶ .of R => g.hom a) h

def affinePointsEquiv : (pointObject R ⟶ pointObject A) ≃ (A →ₐ[ℚ] R) where
  toFun := pointToAlgHom A R
  invFun := pointChange
  left_inv := pointChange_pointToAlgHom A R
  right_inv := pointToAlgHom_pointChange A R

variable {A R} {S : Type} [CommRing S] [Algebra ℚ S]

theorem pointChange_injective : Function.Injective (pointChange (R:=A) (S:=R)) :=
  (affinePointsEquiv A R).symm.injective

theorem pointToAlgHom_natural (f : R →ₐ[ℚ] S) (P : pointObject R ⟶ pointObject A) :
    pointToAlgHom A S (pointChange f ≫ P)=f.comp (pointToAlgHom A R P) := by
  apply pointChange_injective
  rw [pointChange_pointToAlgHom,←pointChange_comp,pointChange_pointToAlgHom]

end FourCorner.ThetaLocalSurvival.Infinitesimal
