import ThetaCoverClassPortable.ThetaNativeFunctionFieldMap
import ThetaCoverClassPortable.SmoothProperRationalPointPlaces
import ThetaCoverClassPortable.SmoothProperClosedPointPlaces
import ThetaCoverClassPortable.NativeStalkFieldNaturality
import ThetaCoverClassPortable.NativeCurveModelExistence
import ThetaCoverClassPortable.Definitions.Def_AlgebraicCurve_CurveModel

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry AlgebraicCurve CategoryTheory
namespace FourCorner.ActualGeometricCoverDeltaComparison
open ThetaNativeFunctionFieldMap NativeStalkFieldNaturality SmoothProperRationalPointPlaces
variable {k : Type} [Field k] [IsAlgClosed k] {X : Scheme} [IsIntegral X]
    (c : X ⟶ Spec (.of k)) [IsProper c] [SmoothOfRelativeDimension 1 c]

theorem actual_model_fieldMap :
    letI := SmoothProperClosedPointPlaces.fieldAlgebra c
    ∀ (M : CurveModel k X.functionField) (i : X ≅ M.C)
    (hgeneric : X.fromSpecStalk (genericPoint X) ≫ i.hom =
      Spec.map (CommRingCat.ofHom M.ffEquiv.symm.toRingHom) ≫ M.C.fromSpecStalk (genericPoint M.C)) ,
    fieldMap i.hom = M.ffEquiv.symm.toRingHom := by
  letI := SmoothProperClosedPointPlaces.fieldAlgebra c
  intro M i hgeneric
  have h : CommRingCat.ofHom (fieldMap i.hom)=CommRingCat.ofHom M.ffEquiv.symm.toRingHom := by
    apply Spec.map_injective
    apply (cancel_mono (M.C.fromSpecStalk (genericPoint M.C))).mp
    rw [generic_diagram,hgeneric]
  exact congrArg CommRingCat.Hom.hom h

/-- A model with the true generic-field comparison sends each actual curve
point to its SAME native function-field place. -/
theorem actual_model_point_place :
    letI := SmoothProperClosedPointPlaces.fieldAlgebra c
    ∀ (M : CurveModel k X.functionField) (i : X ≅ M.C)
    (hi : i.hom ≫ M.toBase=c)
    (hgeneric : X.fromSpecStalk (genericPoint X) ≫ i.hom =
      Spec.map (CommRingCat.ofHom M.ffEquiv.symm.toRingHom) ≫ M.C.fromSpecStalk (genericPoint M.C))
    (P : RationalPoint c),
    M.pointEquivPlace ⟨P.val ≫ i.hom,by rw [Category.assoc,hi];exact P.property⟩ =
      (pointEquivRationalPlace c P).val := by
  letI := SmoothProperClosedPointPlaces.fieldAlgebra c
  intro M i hi hgeneric P
  let P' : RationalPoint M.toBase := ⟨P.val ≫ i.hom,by rw [Category.assoc,hi];exact P.property⟩
  have hM := M.range_stalk_eq (pointEquivClosedPoint M.toBase P')
  have hP := pointEquivRationalPlace_range c P
  have hr := stalk_range_comap i.hom (P.val (IsLocalRing.closedPoint k))
  rw [actual_model_fieldMap c M i hgeneric] at hr
  have hc : (pointEquivClosedPoint M.toBase P').val = i.hom (P.val (IsLocalRing.closedPoint k)) := by
    change (P.val ≫ i.hom) (IsLocalRing.closedPoint k)=_
    rfl
  rw [hc] at hM
  apply Place.ext
  apply SetLike.ext
  intro r
  change r∈(M.placeOfPoint (pointEquivClosedPoint M.toBase P')).toValuationSubring.toSubring ↔
    r∈((pointEquivRationalPlace c P).val).toValuationSubring.toSubring
  rw [←hM,←hP]
  constructor
  · rintro ⟨a,rfl⟩
    have ha : algebraMap (M.C.presheaf.stalk (i.hom (P.val (IsLocalRing.closedPoint k)))) M.C.functionField a∈
        (algebraMap (M.C.presheaf.stalk (i.hom (P.val (IsLocalRing.closedPoint k)))) M.C.functionField).range := ⟨a,rfl⟩
    rw [hr] at ha
    exact ha
  · intro ha
    have hm : M.ffEquiv r∈(algebraMap (M.C.presheaf.stalk (i.hom (P.val (IsLocalRing.closedPoint k)))) M.C.functionField).range := by
      rw [hr]
      change M.ffEquiv.symm (M.ffEquiv r)∈
        (algebraMap (X.presheaf.stalk (P.val (IsLocalRing.closedPoint k))) X.functionField).range
      simpa only [RingEquiv.symm_apply_apply] using ha
    obtain ⟨a,haa⟩ := hm
    refine ⟨a,?_⟩
    change M.ffEquiv.symm (algebraMap _ _ a)=r
    rw [haa,RingEquiv.symm_apply_apply]

end FourCorner.ActualGeometricCoverDeltaComparison
