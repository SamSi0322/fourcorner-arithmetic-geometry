import NativeUnramifiedFinite
import SmoothProperPlaceNaturality
import PlaceDifferentUnramified
import Theorems.Thm_AlgebraicCurve_isClosed_singleton_of_ne_genericPoint
import Mathlib.RingTheory.Unramified.Field

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2500000
set_option synthInstance.maxHeartbeats 400000
set_option linter.style.haveILetI false
open CategoryTheory AlgebraicGeometry AlgebraicCurve
universe u
namespace FourCorner.AllPointStalkUnramified
open SmoothProperClosedPointPlaces SmoothProperRationalPointPlaces SmoothProperPlaceNaturality

theorem formallyUnramified_of_square {A B R S : Type*}
    [CommRing A] [CommRing B] [CommRing R] [CommRing S]
    (f : A →+* B) (g : R →+* S) (eA : A ≃+* R) (eB : B ≃+* S)
    (he : eB.toRingHom.comp f=g.comp eA.toRingHom) (hg : g.FormallyUnramified) :
    f.FormallyUnramified := by
  have hf : f=eB.symm.toRingHom.comp (g.comp eA.toRingHom) := by
    ext a
    have h := RingHom.congr_fun he a
    apply eB.injective
    change eB (f a)=eB (eB.symm (g (eA a)))
    rw [RingEquiv.apply_symm_apply]
    exact h
  rw [hf]
  exact (RingHom.FormallyUnramified.of_surjective eA.surjective).comp hg |>.comp
    (RingHom.FormallyUnramified.of_surjective eB.symm.surjective)

variable {K : Type u} [Field K] {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]

/-- The actual native stalk specialization, with no ambiguous self-algebra instance at eta. -/
def stalkEmbedding (X : Scheme.{u}) [IsIntegral X] (x : X) :
    X.presheaf.stalk x →+* X.functionField :=
  (X.presheaf.stalkSpecializes (genericPoint_specializes x)).hom

/-- The actual generic specialization is identity. -/
theorem generic_embedding (X : Scheme.{u}) [IsIntegral X] :
    stalkEmbedding X (genericPoint X)=RingHom.id _ := by
  unfold stalkEmbedding
  change (X.presheaf.stalkSpecializes (specializes_refl (genericPoint X))).hom = _
  rw [TopCat.Presheaf.stalkSpecializes_refl]
  rfl

theorem embedding_bijective_at_generic (Y : Scheme.{u}) [IsIntegral Y] (y : Y)
    (hy : y=genericPoint Y) : Function.Bijective (stalkEmbedding Y y) := by
  subst y
  rw [generic_embedding Y]
  exact Function.bijective_id

/-- A generic diagram forces the generic point to map to the generic point. -/
theorem image_generic [Algebra Y.functionField X.functionField] (π : X ⟶ Y)
    (hg : X.fromSpecStalk (genericPoint X) ≫ π=
      Spec.map (CommRingCat.ofHom (algebraMap Y.functionField X.functionField)) ≫
        Y.fromSpecStalk (genericPoint Y)) : π (genericPoint X)=genericPoint Y := by
  have h := congrArg (fun f : Spec X.functionField ⟶ Y => f (IsLocalRing.closedPoint X.functionField)) hg
  simp only [Scheme.Hom.comp_apply,Scheme.fromSpecStalk_closedPoint] at h
  have hp : Spec.map (CommRingCat.ofHom (algebraMap Y.functionField X.functionField))
      (IsLocalRing.closedPoint X.functionField)=IsLocalRing.closedPoint Y.functionField := Subsingleton.elim _ _
  have hh := congrArg (fun z : Spec Y.functionField => Y.fromSpecStalk (genericPoint Y) z) hp
  exact h.trans (hh.trans Scheme.fromSpecStalk_closedPoint)

/-- Any actual stalk range equal to a valuation subring gives its actual ring isomorphism. -/
def stalkValuationEquivOfRange (X : Scheme.{u}) [IsIntegral X] (x : X)
    (V : ValuationSubring X.functionField)
    (h : (algebraMap (X.presheaf.stalk x) X.functionField).range=V.toSubring) :
    X.presheaf.stalk x ≃+* V := by
  let g := algebraMap (X.presheaf.stalk x) X.functionField
  let f := g.codRestrict V.toSubring (fun a => by rw [←h];exact ⟨a,rfl⟩)
  apply RingEquiv.ofBijective f
  constructor
  · intro a b he
    apply IsFractionRing.injective (X.presheaf.stalk x) X.functionField
    exact congrArg Subtype.val he
  · intro a
    have ha : (a : X.functionField)∈g.range := by rw [h];exact a.property
    obtain ⟨b,hb⟩ := ha
    exact ⟨b,Subtype.ext hb⟩

@[simp] theorem stalkValuationEquivOfRange_coe (X : Scheme.{u}) [IsIntegral X] (x : X)
    (V : ValuationSubring X.functionField)
    (h : (algebraMap (X.presheaf.stalk x) X.functionField).range=V.toSubring)
    (a : X.presheaf.stalk x) :
    ((stalkValuationEquivOfRange X x V h a : V) : X.functionField)=
      algebraMap (X.presheaf.stalk x) X.functionField a := rfl

variable (cX : X ⟶ Spec (.of K)) (cY : Y ⟶ Spec (.of K))
  [SmoothOfRelativeDimension 1 cX] [SmoothOfRelativeDimension 1 cY] [IsProper cX] [IsProper cY]
  [Algebra Y.functionField X.functionField]

/-- Every actual pair of closed centres is compatible with restriction; no K-rationality is required. -/
theorem closed_point_comap [FiniteDimensional Y.functionField X.functionField]
    (htower : letI := fieldAlgebra cX;letI := fieldAlgebra cY;IsScalarTower K Y.functionField X.functionField)
    (π : X ⟶ Y)
    (hg : X.fromSpecStalk (genericPoint X) ≫ π=
      Spec.map (CommRingCat.ofHom (algebraMap Y.functionField X.functionField)) ≫
        Y.fromSpecStalk (genericPoint Y)) (x : closedPoints X)
    (hy : IsClosed ({π x.val} : Set Y)) :
    letI := fieldAlgebra cX;letI := fieldAlgebra cY;letI := htower
    (algebraMap (Y.presheaf.stalk (π x.val)) Y.functionField).range=
      ((placeOfClosedPoint cX x).restrict Y.functionField).toValuationSubring.toSubring := by
  letI := fieldAlgebra cX
  letI := fieldAlgebra cY
  letI := htower
  let w := placeOfClosedPoint cX x
  let v := placeOfClosedPoint cY ⟨π x.val,hy⟩
  have hx := range_stalk cX x
  have hy' := range_stalk cY ⟨π x.val,hy⟩
  have hle : v.toValuationSubring≤w.toValuationSubring.comap (algebraMap Y.functionField X.functionField) := by
    intro a ha
    have hm : a∈(algebraMap (Y.presheaf.stalk (π x.val)) Y.functionField).range := by rw [hy'];exact ha
    obtain ⟨b,hb⟩ := hm
    change algebraMap Y.functionField X.functionField a∈w.toValuationSubring
    have hn := stalk_field_naturality π hg x.val b
    rw [hb] at hn
    rw [hn]
    change _∈w.toValuationSubring.toSubring
    rw [←hx]
    exact ⟨_,rfl⟩
  have he : v.toValuationSubring=(w.restrict Y.functionField).toValuationSubring :=
    ValuationSubring.eq_of_le_of_ne_top v.toValuationSubring hle (w.restrict Y.functionField).ne_top'
  exact hy'.trans (congrArg ValuationSubring.toSubring he)

#print axioms formallyUnramified_of_square
#print axioms generic_embedding
#print axioms image_generic
#print axioms stalkValuationEquivOfRange
#print axioms closed_point_comap
end FourCorner.AllPointStalkUnramified
