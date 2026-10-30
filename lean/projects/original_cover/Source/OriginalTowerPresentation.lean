import OriginalDiagonalPresentation
import geometry.MultiquadraticCoordinateUniversal

/-! An independent iterated monic-root presentation of the actual original surface. -/
noncomputable section
namespace FourCorner.OriginalCoverCompletion.OriginalTower
open Polynomial
open FourCorner.Multiquadratic

abbrev Coeff := Polynomial (Polynomial ℚ)
def x : Coeff := C X
def y : Coeff := X
def radicand : Fin 4 → Coeff
 | 0 => x^2+y^2
 | 1 => (x-1)^2+y^2
 | 2 => x^2+(y-1)^2
 | 3 => (x-1)^2+(y-1)^2
def radiusIndex : Fin 4 → Fin 6 | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 5
abbrev Third := FourCorner.Multiquadratic.CoordinateAlgebra.Stage₃ Coeff (radicand 0) (radicand 1) (radicand 2)
def fourthEquation : Third[X] := X^2-C (algebraMap Coeff Third (radicand 3))
abbrev Ring := AdjoinRoot fourthEquation

def coords : Fin 6 → Ring :=
 ![algebraMap Coeff Ring x, algebraMap Coeff Ring y,
   algebraMap Third Ring (FourCorner.Multiquadratic.CoordinateAlgebra.coordinate₁ Coeff (radicand 0) (radicand 1) (radicand 2)),
   algebraMap Third Ring (FourCorner.Multiquadratic.CoordinateAlgebra.coordinate₂ Coeff (radicand 0) (radicand 1) (radicand 2)),
   algebraMap Third Ring (FourCorner.Multiquadratic.CoordinateAlgebra.coordinate₃ Coeff (radicand 0) (radicand 1) (radicand 2)),
   AdjoinRoot.root fourthEquation]

 theorem fourth_square : (AdjoinRoot.root fourthEquation)^2 = algebraMap Coeff Ring (radicand 3) := by
  have h := AdjoinRoot.eval₂_root fourthEquation
  change (X^2-C (algebraMap Coeff Third (radicand 3))).eval₂ (algebraMap Third Ring)
    (AdjoinRoot.root fourthEquation)=0 at h
  rw [eval₂_sub,eval₂_pow,eval₂_X,eval₂_C,sub_eq_zero] at h
  exact h

 theorem coords_square (i : Fin 4) : (coords (radiusIndex i))^2=algebraMap Coeff Ring (radicand i) := by
  fin_cases i
  · change (algebraMap Third Ring (CoordinateAlgebra.coordinate₁ Coeff (radicand 0) (radicand 1) (radicand 2)))^2=_
    rw [← map_pow,CoordinateAlgebra.coordinate₁_sq]
    rfl
  · change (algebraMap Third Ring (CoordinateAlgebra.coordinate₂ Coeff (radicand 0) (radicand 1) (radicand 2)))^2=_
    rw [← map_pow,CoordinateAlgebra.coordinate₂_sq]
    rfl
  · change (algebraMap Third Ring (CoordinateAlgebra.coordinate₃ Coeff (radicand 0) (radicand 1) (radicand 2)))^2=_
    rw [← map_pow,CoordinateAlgebra.coordinate₃_sq]
    rfl
  · exact fourth_square

 theorem coords_relations : ∀ i, originalRelations coords i=0 := by
  intro i
  have hi := coords_square i
  fin_cases i <;> simp only [radiusIndex,radicand,map_add,map_sub,map_pow,map_one] at hi
  all_goals simp only [originalRelations,Matrix.cons_val_zero,Matrix.cons_val_zero',Matrix.cons_val_succ',
    show coords 0=algebraMap Coeff Ring x from rfl,show coords 1=algebraMap Coeff Ring y from rfl]
  all_goals linear_combination hi

def toTower : OriginalRing →ₐ[ℚ] Ring := originalLift coords coords_relations

@[simp] theorem toTower_coordinate (i) : toTower (originalCoordinates i)=coords i :=
 originalLift_coordinate _ _ _

def coeffReturn : Coeff →ₐ[ℚ] OriginalRing :=
  Polynomial.aevalTower (Polynomial.aeval (originalCoordinates 0)) (originalCoordinates 1)

@[simp] theorem coeffReturn_x : coeffReturn x=originalCoordinates 0 := by
  simp [coeffReturn,x,Polynomial.aevalTower]
@[simp] theorem coeffReturn_y : coeffReturn y=originalCoordinates 1 := by
  simp [coeffReturn,y,Polynomial.aevalTower]

 theorem return_squares (i : Fin 4) : (originalCoordinates (radiusIndex i))^2=coeffReturn (radicand i) := by
  have h := original_coordinates_relations i
  fin_cases i <;> simp [radiusIndex,radicand,originalRelations,map_add,map_sub,map_pow] at h ⊢ <;>
    linear_combination h

def thirdReturn : Third →ₐ[ℚ] OriginalRing :=
  FourCorner.Multiquadratic.CoordinateUniversal.liftAlgHom Coeff OriginalRing coeffReturn (radicand 0) (radicand 1) (radicand 2)
    (originalCoordinates 2) (originalCoordinates 3) (originalCoordinates 4)
    (return_squares 0) (return_squares 1) (return_squares 2)

@[simp] theorem thirdReturn_coeff (p : Coeff) :
    thirdReturn (algebraMap Coeff Third p)=coeffReturn p :=
  CoordinateUniversal.lift_algebraMap Coeff OriginalRing coeffReturn.toRingHom
    (radicand 0) (radicand 1) (radicand 2) (originalCoordinates 2) (originalCoordinates 3)
    (originalCoordinates 4) (return_squares 0) (return_squares 1) (return_squares 2) p

@[simp] theorem thirdReturn_coordinate₁ : thirdReturn
    (CoordinateAlgebra.coordinate₁ Coeff (radicand 0) (radicand 1) (radicand 2))=originalCoordinates 2 :=
  CoordinateUniversal.lift_coordinate₁ Coeff OriginalRing coeffReturn.toRingHom
    (radicand 0) (radicand 1) (radicand 2) (originalCoordinates 2) (originalCoordinates 3)
    (originalCoordinates 4) (return_squares 0) (return_squares 1) (return_squares 2)
@[simp] theorem thirdReturn_coordinate₂ : thirdReturn
    (CoordinateAlgebra.coordinate₂ Coeff (radicand 0) (radicand 1) (radicand 2))=originalCoordinates 3 :=
  CoordinateUniversal.lift_coordinate₂ Coeff OriginalRing coeffReturn.toRingHom
    (radicand 0) (radicand 1) (radicand 2) (originalCoordinates 2) (originalCoordinates 3)
    (originalCoordinates 4) (return_squares 0) (return_squares 1) (return_squares 2)
@[simp] theorem thirdReturn_coordinate₃ : thirdReturn
    (CoordinateAlgebra.coordinate₃ Coeff (radicand 0) (radicand 1) (radicand 2))=originalCoordinates 4 :=
  CoordinateUniversal.lift_coordinate₃ Coeff OriginalRing coeffReturn.toRingHom
    (radicand 0) (radicand 1) (radicand 2) (originalCoordinates 2) (originalCoordinates 3)
    (originalCoordinates 4) (return_squares 0) (return_squares 1) (return_squares 2)

theorem fourthReturn_root : fourthEquation.eval₂ thirdReturn.toRingHom (originalCoordinates 5)=0 := by
  simp only [fourthEquation,eval₂_sub,eval₂_pow,eval₂_X,eval₂_C]
  change originalCoordinates 5^2-thirdReturn (algebraMap Coeff Third (radicand 3))=0
  rw [thirdReturn_coeff]
  exact sub_eq_zero.mpr (return_squares 3)

def fromTower : Ring →ₐ[ℚ] OriginalRing :=
  AdjoinRoot.liftAlgHom fourthEquation thirdReturn (originalCoordinates 5) fourthReturn_root

@[simp] theorem fromTower_of (p : Third) :
    fromTower (algebraMap Third Ring p)=thirdReturn p :=
  AdjoinRoot.lift_of fourthReturn_root
@[simp] theorem fromTower_root :
    fromTower (AdjoinRoot.root fourthEquation)=originalCoordinates 5 :=
  AdjoinRoot.lift_root fourthReturn_root
@[simp] theorem fromTower_coeff (p : Coeff) : fromTower (algebraMap Coeff Ring p)=coeffReturn p := by
  rw [IsScalarTower.algebraMap_apply Coeff Third Ring,fromTower_of,thirdReturn_coeff]

@[simp] theorem fromTower_coords (i : Fin 6) : fromTower (coords i)=originalCoordinates i := by
  fin_cases i
  · exact (fromTower_coeff x).trans coeffReturn_x
  · exact (fromTower_coeff y).trans coeffReturn_y
  · exact (fromTower_of _).trans thirdReturn_coordinate₁
  · exact (fromTower_of _).trans thirdReturn_coordinate₂
  · exact (fromTower_of _).trans thirdReturn_coordinate₃
  · exact fromTower_root

 theorem original_comp : fromTower.comp toTower=AlgHom.id ℚ OriginalRing := by
  apply original_ext
  intro i
  change fromTower (toTower (originalCoordinates i))=originalCoordinates i
  simp

 theorem ext {A : Type*} [CommRing A] [Algebra ℚ A] {f g : Ring →ₐ[ℚ] A}
    (h : ∀ i, f (coords i)=g (coords i)) : f=g := by
  apply AlgHom.coe_ringHom_injective
  apply AdjoinRoot.ringHom_ext
  · apply FourCorner.Multiquadratic.CoordinateUniversal.ringHom_ext Coeff A (radicand 0) (radicand 1) (radicand 2)
    · intro p
      have hc : f.toRingHom.comp (algebraMap Coeff Ring)=g.toRingHom.comp (algebraMap Coeff Ring) := by
        apply Polynomial.ringHom_ext'
        · apply Polynomial.ringHom_ext'
          · ext q
            exact (f.commutes q).trans (g.commutes q).symm
          · exact h 0
        · exact h 1
      exact RingHom.congr_fun hc p
    · exact h 2
    · exact h 3
    · exact h 4
  · exact h 5


 theorem tower_comp : toTower.comp fromTower=AlgHom.id ℚ Ring := by
  apply ext
  intro i
  change toTower (fromTower (coords i))=coords i
  rw [fromTower_coords]
  exact toTower_coordinate i

/-- Exact actual-coordinate algebra isomorphism, with no field or domain assumptions. -/
def equiv : OriginalRing ≃ₐ[ℚ] Ring :=
 AlgEquiv.ofAlgHom toTower fromTower tower_comp original_comp

#print axioms equiv
#print axioms coords_relations
end FourCorner.OriginalCoverCompletion.OriginalTower
