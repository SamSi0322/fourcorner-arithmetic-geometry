import ThetaLocalSurvivalPortable.ActualAbelianMultiplication
import ThetaLocalSurvivalPortable.SquareZeroScalars
import Mathlib.RingTheory.Derivation.ToSquareZero

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.MonObj FourCorner.ThetaLocalSurvival.SquareZeroScalars
namespace FourCorner.ThetaLocalSurvival.Infinitesimal
open Multiplication

abbrev pointObject (R : Type) [CommRing R] [Algebra ℚ R] : Over base :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℚ R)))

variable {R S T : Type} [CommRing R] [CommRing S] [CommRing T]
  [Algebra ℚ R] [Algebra ℚ S] [Algebra ℚ T]

def pointChange (f : R →ₐ[ℚ] S) : pointObject S ⟶ pointObject R :=
  Over.homMk (Spec.map (CommRingCat.ofHom f.toRingHom)) (by
    change Spec.map (CommRingCat.ofHom f.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap ℚ R))=Spec.map (CommRingCat.ofHom (algebraMap ℚ S))
    rw [←Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    exact f.comp_algebraMap)

@[simp] theorem pointChange_comp (f : R →ₐ[ℚ] S) (g : S →ₐ[ℚ] T) :
    pointChange g ≫ pointChange f=pointChange (g.comp f) := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom g.toRingHom) ≫ Spec.map (CommRingCat.ofHom f.toRingHom)=_
  rw [←Spec.map_comp]
  rfl

@[simp] theorem pointChange_id : pointChange (AlgHom.id ℚ R)=𝟙 (pointObject R) := by
  apply Over.OverMorphism.ext
  exact Spec.map_id _

variable (G : Over base) [GrpObj G]
abbrev points (R : Type) [CommRing R] [Algebra ℚ R] := pointObject R ⟶ G

def change (f : R →ₐ[ℚ] S) : points G R →* points G S where
  toFun P := pointChange f ≫ P
  map_one' := MonObj.comp_one _
  map_mul' _ _ := MonObj.comp_mul _ _ _

@[simp] theorem change_comp (f : R →ₐ[ℚ] S) (g : S →ₐ[ℚ] T) (P : points G R) :
    change G g (change G f P)=change G (g.comp f) P := by
  simp only [change,MonoidHom.coe_mk,OneHom.coe_mk,←Category.assoc,pointChange_comp]

@[simp] theorem change_id (P : points G R) : change G (AlgHom.id ℚ R) P=P := by
  simp [change]

variable (M : Type) [AddCommGroup M] [Module ℚ M]
abbrev sq := TrivSqZeroExt ℚ M

def reduction : points G (sq M) →* points G ℚ :=
  change G (TrivSqZeroExt.fstHom ℚ ℚ M)

/-- The actual kernel of reduction on scheme-valued points; its elements
are genuine over-QQ morphisms Spec(QQ⊕M)→G reducing to identity. -/
abbrev tangentPoints := (reduction G M).ker

variable {M} {N : Type} [AddCommGroup N] [Module ℚ N]

def tangentMap (f : M →ₗ[ℚ] N) : tangentPoints G M →* tangentPoints G N where
  toFun P := ⟨change G (TrivSqZeroExt.map f) P.val,by
    change change G (TrivSqZeroExt.fstHom ℚ ℚ N)
      (change G (TrivSqZeroExt.map f) P.val)=1
    rw [change_comp,TrivSqZeroExt.fstHom_comp_map]
    exact P.property⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)

@[simp] theorem tangentMap_val (f : M →ₗ[ℚ] N) (P : tangentPoints G M) :
    (tangentMap G f P).val=change G (TrivSqZeroExt.map f) P.val := rfl

@[simp] theorem tangentMap_comp {L : Type} [AddCommGroup L] [Module ℚ L]
    (f : M →ₗ[ℚ] N) (g : N →ₗ[ℚ] L) (P : tangentPoints G M) :
    tangentMap G g (tangentMap G f P)=tangentMap G (g.comp f) P := by
  apply Subtype.ext
  simp only [tangentMap_val,change_comp,TrivSqZeroExt.map_comp_map]

@[simp] theorem tangentMap_id (P : tangentPoints G M) :
    tangentMap G (LinearMap.id : M →ₗ[ℚ] M) P=P := by
  apply Subtype.ext
  simp only [tangentMap_val,TrivSqZeroExt.map_id,change_id]

/-- The actual multiplication morphism acts by the group power on the
actual infinitesimal point kernel, before any linear identification. -/
theorem multiplication_on_tangentPoints (P : tangentPoints G M) (m : ℕ) :
    P.val ≫ multiplicationOver G m=(P^m).val := by
  rw [multiplication_points]
  rfl

end FourCorner.ThetaLocalSurvival.Infinitesimal
