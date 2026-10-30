import ThetaCoverClassPortable.ThetaUnramifiedPlaceIndex
import ThetaCoverClassPortable.ThetaDActualFieldCover
import ThetaCoverClassPortable.SmoothProperClosedPointPlaces
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified

namespace FourCorner.ThetaEtaleAllPlaces
open AlgebraicGeometry AlgebraicCurve CategoryTheory
open ThetaNativeFunctionFieldMap SmoothProperClosedPointPlaces
noncomputable section
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u

 theorem field_stalk_diagram (X : Scheme) [IsIntegral X] (x : X) :
    Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) X.functionField)) ≫ X.fromSpecStalk x=
      X.fromSpecStalk (genericPoint X) := by
  exact Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes x)

variable {X Y : Scheme} [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [Surjective f]

 theorem stalk_field_naturality (x : X) (a : Y.presheaf.stalk (f x)) :
    fieldMap f (algebraMap (Y.presheaf.stalk (f x)) Y.functionField a)=
      algebraMap (X.presheaf.stalk x) X.functionField ((f.stalkMap x).hom a) := by
  have he : CommRingCat.ofHom ((fieldMap f).comp (algebraMap (Y.presheaf.stalk (f x)) Y.functionField))=
      CommRingCat.ofHom ((algebraMap (X.presheaf.stalk x) X.functionField).comp (f.stalkMap x).hom) := by
    apply Spec.map_injective
    apply (cancel_mono (Y.fromSpecStalk (f x))).mp
    rw [CommRingCat.ofHom_comp,CommRingCat.ofHom_comp,Spec.map_comp,Spec.map_comp]
    simp only [CommRingCat.ofHom_hom,Category.assoc]
    rw [field_stalk_diagram,generic_diagram,
      Scheme.SpecMap_stalkMap_fromSpecStalk,←Category.assoc,field_stalk_diagram]
  exact congrArg (fun g : Y.presheaf.stalk (f x) ⟶ X.presheaf.stalk (genericPoint X) => g.hom a) he

 def valuationEquivOfRange (X : Scheme) [IsIntegral X] (x : X) (V : ValuationSubring X.functionField)
    (h : (algebraMap (X.presheaf.stalk x) X.functionField).range=V.toSubring) :
    X.presheaf.stalk x ≃+* V := by
  let g := algebraMap (X.presheaf.stalk x) X.functionField
  let l := g.codRestrict V.toSubring (fun a => by rw [←h];exact ⟨a,rfl⟩)
  apply RingEquiv.ofBijective l
  constructor
  · intro a b he
    exact IsFractionRing.injective (X.presheaf.stalk x) X.functionField (congrArg Subtype.val he)
  · intro a
    have ha : (a : X.functionField)∈g.range := by rw [h];exact a.property
    obtain ⟨b,hb⟩ := ha
    exact ⟨b,Subtype.ext hb⟩

variable {K : Type} [Field K] (cX : X ⟶ Spec (.of K)) (cY : Y ⟶ Spec (.of K))
  [SmoothOfRelativeDimension 1 cX] [SmoothOfRelativeDimension 1 cY] [IsProper cX] [IsProper cY]

 theorem native_tower (he : f ≫ cY=cX) :
    letI := fieldAlgebra cX;letI := fieldAlgebra cY
    letI : Algebra Y.functionField X.functionField := (fieldMap f).toAlgebra
    IsScalarTower K Y.functionField X.functionField := by
  letI := fieldAlgebra cX;letI := fieldAlgebra cY
  letI : Algebra Y.functionField X.functionField := (fieldMap f).toAlgebra
  exact IsScalarTower.of_algebraMap_eq fun a => (base_compatibility f cX cY he a).symm

 theorem closed_range_comap (he : f ≫ cY=cX)
    (hfd : letI : Algebra Y.functionField X.functionField := (fieldMap f).toAlgebra;
      FiniteDimensional Y.functionField X.functionField)
    (x : closedPoints X) (hy : IsClosed ({f x.val} : Set Y)) :
    letI := fieldAlgebra cX;letI := fieldAlgebra cY
    letI : Algebra Y.functionField X.functionField := (fieldMap f).toAlgebra
    letI := hfd
    letI := native_tower f cX cY he
    (algebraMap (Y.presheaf.stalk (f x.val)) Y.functionField).range=
      ((placeOfClosedPoint cX x).restrict Y.functionField).toValuationSubring.toSubring := by
  letI := fieldAlgebra cX;letI := fieldAlgebra cY
  letI : Algebra Y.functionField X.functionField := (fieldMap f).toAlgebra
  letI := hfd
  letI := native_tower f cX cY he
  let w := placeOfClosedPoint cX x
  let v := placeOfClosedPoint cY ⟨f x.val,hy⟩
  have hx := range_stalk cX x
  have hy' := range_stalk cY ⟨f x.val,hy⟩
  have hle : v.toValuationSubring ≤ w.toValuationSubring.comap (algebraMap Y.functionField X.functionField) := by
    intro a ha
    have hm : a∈(algebraMap (Y.presheaf.stalk (f x.val)) Y.functionField).range := by rw [hy'];exact ha
    obtain ⟨b,hb⟩ := hm
    change fieldMap f a ∈ w.toValuationSubring
    rw [←hb,stalk_field_naturality]
    change _∈w.toValuationSubring.toSubring
    rw [←hx]
    exact ⟨_,rfl⟩
  have hr : v.toValuationSubring=(w.restrict Y.functionField).toValuationSubring :=
    ValuationSubring.eq_of_le_of_ne_top v.toValuationSubring hle (w.restrict Y.functionField).ne_top'
  exact hy'.trans (congrArg ValuationSubring.toSubring hr)

variable [IsFinite f] [Etale f]

/-- Every ACTUAL place of the ACTUAL source field is unramified under a
native finite etale constant-rank-two covering of smooth proper curves. -/
theorem all_index_one (he : f ≫ cY=cX) (hrank : ∀y,f.finrank y=2) :
    letI := fieldAlgebra cX;letI := fieldAlgebra cY
    letI : Algebra Y.functionField X.functionField := (fieldMap f).toAlgebra
    letI : FiniteDimensional Y.functionField X.functionField :=
      Module.finite_of_finrank_pos (by rw [ThetaFiniteGenericDegree.degree_two f hrank];decide)
    ∀w : Place K X.functionField,w.ramificationIndex Y.functionField=1 := by
  letI := fieldAlgebra cX;letI := fieldAlgebra cY
  letI : Algebra Y.functionField X.functionField := (fieldMap f).toAlgebra
  have hfd : FiniteDimensional Y.functionField X.functionField :=
    Module.finite_of_finrank_pos (by rw [ThetaFiniteGenericDegree.degree_two f hrank];decide)
  letI := hfd
  letI := native_tower f cX cY he
  intro w
  obtain ⟨x,hx⟩ := (closedPointPlaceEquiv cX).surjective w
  change placeOfClosedPoint cX x=w at hx
  rw [←hx]
  let w := placeOfClosedPoint cX x
  have hy : IsClosed ({f x.val} : Set Y) := by
    simpa only [Set.image_singleton] using f.isClosedMap _ x.property
  let eA := valuationEquivOfRange Y (f x.val) (w.restrict Y.functionField).toValuationSubring
    (closed_range_comap f cX cY he hfd x hy)
  let eB := stalkValuationEquiv cX x
  let g := Place.restrictInclusion Y.functionField w
  have hsq : g.comp eA.toRingHom=eB.toRingHom.comp (f.stalkMap x.val).hom := by
    ext a
    change fieldMap f (algebraMap (Y.presheaf.stalk (f x.val)) Y.functionField a)=
      algebraMap (X.presheaf.stalk x.val) X.functionField ((f.stalkMap x.val).hom a)
    exact stalk_field_naturality f x.val a
  obtain ⟨hu,ht⟩ := ThetaUnramifiedPlaceIndex.transport_properties
    (f.stalkMap x.val).hom g eA eB hsq
    (FormallyUnramified.stalkMap f x.val) (LocallyOfFiniteType.stalkMap f x.val)
  exact ThetaUnramifiedPlaceIndex.index_one w hu ht

#print axioms stalk_field_naturality
#print axioms native_tower
#print axioms closed_range_comap
#print axioms all_index_one
end
end FourCorner.ThetaEtaleAllPlaces
