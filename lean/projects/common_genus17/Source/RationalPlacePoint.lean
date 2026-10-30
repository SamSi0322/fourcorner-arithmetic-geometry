import CommonPostPointResidue
import Mathlib.AlgebraicGeometry.ResidueField

noncomputable section
open AlgebraicGeometry AlgebraicCurve CategoryTheory
namespace FourCorner.RationalPlacePoint
open CommonPostPointResidue CommonRationalPlace CurveRationalPlace07

theorem field_hom_to_rat_unique {F : Type*} [Field F] (f g : F →+* ℚ) : f = g := by
  letI : CharZero F := f.charZero
  apply RingHom.ext
  intro a
  have ha : a = (f a : ℚ) := by
    apply f.injective
    simp only [map_ratCast,Rat.cast_id]
  calc
    f a = g ((f a : ℚ) : F) := by simp only [map_ratCast,Rat.cast_id]
    _ = g a := congrArg g ha.symm

/-- An actual rational scheme point is uniquely determined by its underlying
point: embeddings of a residue field into the prime field Q are unique. -/
theorem point_ext {X : Scheme} (p q : Spec (.of ℚ) ⟶ X)
    (h : p (IsLocalRing.closedPoint ℚ) = q (IsLocalRing.closedPoint ℚ)) : p = q := by
  apply (Scheme.SpecToEquivOfField ℚ X).injective
  apply Scheme.SpecToEquivOfField_eq_iff.mpr
  refine ⟨h,?_⟩
  apply CommRingCat.hom_ext
  exact field_hom_to_rat_unique _ _

theorem valuation_eval_surjective {F : Type*} [Field F] [Algebra ℚ F]
    (w : Place ℚ F) (f : w.toValuationSubring →+* ℚ) : Function.Surjective f := by
  intro q
  refine ⟨algebraMap ℚ w.toValuationSubring q,?_⟩
  exact congrArg (fun g : ℚ →+* ℚ => g q)
    (Subsingleton.elim (f.comp (algebraMap ℚ w.toValuationSubring)) (RingHom.id ℚ))

variable {F : Type*} [Field F] [Algebra ℚ F]

/-- Realize a rational valuation-ring evaluation on the actual local stalk
of the given curve model and then its actual Scheme. -/
def pointFromEval (M : CurveModel ℚ F) (x : closedPoints M.C)
    (f : (M.placeOfPoint x).toValuationSubring →+* ℚ) : Spec (.of ℚ) ⟶ M.C :=
  Spec.map (CommRingCat.ofHom (f.comp (stalkValuationEquiv M x).toRingHom)) ≫ M.C.fromSpecStalk x.1

theorem pointFromEval_image (M : CurveModel ℚ F) (x : closedPoints M.C)
    (f : (M.placeOfPoint x).toValuationSubring →+* ℚ) :
    pointFromEval M x f (IsLocalRing.closedPoint ℚ) = x.1 := by
  haveI : IsLocalHom (f.comp (stalkValuationEquiv M x).toRingHom) :=
    IsLocalHom.of_surjective _ ((valuation_eval_surjective _ f).comp
      (stalkValuationEquiv M x).surjective)
  change M.C.fromSpecStalk x.1
    ((Spec.map (CommRingCat.ofHom (f.comp (stalkValuationEquiv M x).toRingHom)))
      (IsLocalRing.closedPoint ℚ)) = x.1
  rw [Spec_closedPoint,Scheme.fromSpecStalk_closedPoint]

theorem pointFromEval_center (M : CurveModel ℚ F) (x : closedPoints M.C)
    (f : (M.placeOfPoint x).toValuationSubring →+* ℚ) :
    pointCenter M (pointFromEval M x f) = x := by
  apply Subtype.ext
  exact pointFromEval_image M x f

def pointOfPlace (M : CurveModel ℚ F) (w : Place ℚ F) (hw : w.IsRational) :
    Spec (.of ℚ) ⟶ M.C := by
  let x := M.placeEquiv.symm w
  have hx : M.placeOfPoint x = w := M.placeEquiv.apply_symm_apply w
  have hwx : (M.placeOfPoint x).IsRational := hx.symm ▸ hw
  exact pointFromEval M x (rationalEval (M.placeOfPoint x) hwx).toRingHom

/-- The construction retains the supplied rational place exactly. -/
theorem pointOfPlace_place (M : CurveModel ℚ F) (w : Place ℚ F) (hw : w.IsRational) :
    pointPlace M (pointOfPlace M w hw) = w := by
  unfold pointOfPlace
  dsimp only
  rw [pointPlace,pointFromEval_center]
  exact M.placeEquiv.apply_symm_apply w

theorem point_place_injective (M : CurveModel ℚ F) :
    Function.Injective (pointPlace M) := by
  intro p q h
  have hc := M.placeOfPoint_bijective.injective h
  apply point_ext
  exact congrArg Subtype.val hc

end FourCorner.RationalPlacePoint
#print axioms FourCorner.RationalPlacePoint.point_ext
#print axioms FourCorner.RationalPlacePoint.pointOfPlace_place
#print axioms FourCorner.RationalPlacePoint.point_place_injective
